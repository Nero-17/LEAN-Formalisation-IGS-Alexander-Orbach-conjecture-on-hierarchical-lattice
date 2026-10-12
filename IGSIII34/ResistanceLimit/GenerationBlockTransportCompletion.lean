import IGSIII34.ResistanceLimit.GenerationBlockEnergyCompletion

/-! Exact transport, not merely an inequality, for source energies in actual
IGS block decompositions. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

theorem stationary_generation_block_source_energy_transport
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ) :
    sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened))
      (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) address edge.val) potential =
    sourceComponentEnergy (substitutedNetwork (rule.generation coarse).network (rule.generation fine).network
      (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened edge)))
      (fun edge => growth⁻¹ ^ (coarse + fine + 2) * field
        ((address ++ generationEdgeAddress rule coarse edge.1) ++ generationEdgeAddress rule fine edge.2.val))
      (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex))) := by
  have transport := sourceComponentEnergy_network_equivalence
    (rule.generationBlockDecomposition coarse fine)
    (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)
    (stationaryGenerationResistance rule field growth (coarse + fine + 1) address)
    (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm vertex))
  simp only [Equiv.symm_apply_apply] at transport
  rw [marked_generation_block_configuration rule marks coarse fine address opened] at transport
  have resistanceIdentity :
      (fun edge : {edge : Fin ((rule.generation coarse).edges * (rule.generation fine).edges) //
        substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks fine
          (address ++ generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse address opened edge)) edge = true} =>
        stationaryGenerationResistance rule field growth (coarse + fine + 1) address
          ((rule.generationBlockDecomposition coarse fine).edge.symm edge.val)) =
      (fun edge => growth⁻¹ ^ (coarse + fine + 2) * field
        ((address ++ generationEdgeAddress rule coarse ((substitutionOpenEdgeEquiv
          (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
            (markedGenerationConfiguration rule marks coarse address opened edge))).symm edge).1) ++
          generationEdgeAddress rule fine ((substitutionOpenEdgeEquiv
            (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
              (markedGenerationConfiguration rule marks coarse address opened edge))).symm edge).2.val)) := by
    funext edge
    have reconstruct := congrArg Subtype.val ((substitutionOpenEdgeEquiv
      (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened edge))).apply_symm_apply edge)
    change finProdFinEquiv _ = edge.val at reconstruct
    unfold stationaryGenerationResistance
    rw [← reconstruct, generationEdgeAddress_block]
    simp only [List.append_assoc, Nat.add_assoc]
  rw [resistanceIdentity] at transport
  rw [sourceComponentEnergy_reindex
    (substitutedNetwork (rule.generation coarse).network (rule.generation fine).network
      (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened edge)))
    (network ((rule.generation coarse).network.substitute (rule.generation fine).network)
      (substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks fine
        (address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened edge))))
    (Fintype.equivFin _) (substitutionOpenEdgeEquiv _)
    (fun edge => (rule.generation coarse).network.substitute_endpoint (rule.generation fine).network edge.1 edge.2.val)
    rfl
    (fun edge => growth⁻¹ ^ (coarse + fine + 2) * field
      ((address ++ generationEdgeAddress rule coarse edge.1) ++ generationEdgeAddress rule fine edge.2.val))
    (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm vertex))] at transport
  exact transport.symm

end
end IGSIII34.ResistanceLimit
