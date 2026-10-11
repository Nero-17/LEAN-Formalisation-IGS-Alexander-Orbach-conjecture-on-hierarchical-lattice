import IGSIII34.ResistanceLimit.StationaryBlockTraceCompletion20261011
import IGSIII34.Percolation.NetworkEquivalence
import IGSIII.Geometry.ActualBlockCellEmbedding

/-! Actual finite-generation source-energy transport under arbitrary block
decompositions. The graph, edge addresses, old vertices and source are all
the original indexed IGS objects. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

theorem sourceComponentEnergy_network_equivalence
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : Universality.FiniteNetwork firstVertices firstEdges}
    {second : Universality.FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges)
    (resistance : Fin firstEdges → ℝ) (potential : Fin secondVertices → ℝ) :
    sourceComponentEnergy (network second (equivalence.configuration configuration))
      (fun edge => resistance (equivalence.edge.symm edge.val)) potential =
    sourceComponentEnergy (network first configuration) (fun edge => resistance edge.val)
      (fun vertex => potential (equivalence.vertex vertex)) := by
  have reindexed := sourceComponentEnergy_reindex (network first configuration)
    (network second (equivalence.configuration configuration)) equivalence.vertex
    (networkEquivalenceOpenEdges equivalence configuration)
    (fun edge => equivalence.endpoint edge.val) equivalence.source.symm
    (fun edge => resistance edge.val) potential
  exact reindexed

theorem marked_generation_block_configuration
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    (rule.generationBlockDecomposition coarse fine).configuration
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) =
    substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks fine
      (address ++ generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse address opened edge)) := by
  funext leaf
  obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective leaf
  change markedGenerationConfiguration rule marks (coarse + fine + 1) address opened
      ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child))) = _
  simpa only [generationBlockCells_apply, substitutionConfigurationEquiv, Equiv.coe_fn_mk,
    Equiv.symm_apply_apply] using
      congrFun (generationBlockCells_marked rule marks coarse fine address opened edge) child

theorem stationary_block_generation_coefficient
    (growth : ℝ) (growthPositive : 0 < growth) (coarse fine : ℕ) :
    growth⁻¹ ^ (coarse + fine + 2) * growth ^ (fine + 1) = growth⁻¹ ^ (coarse + 1) := by
  rw [show coarse + fine + 2 = (coarse + 1) + (fine + 1) by omega,
    pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ growthPositive.ne', one_pow, mul_one]

theorem stationary_generation_block_source_energy_le
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ) :
    sourceComponentEnergy (network (rule.generation coarse).network
      (markedGenerationConfiguration rule marks coarse address opened))
      (fun edge => stationaryGenerationResistance rule field growth coarse address edge.val)
      (fun vertex => potential (blockOldVertexEmbedding rule coarse fine vertex)) ≤
    sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened))
      (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) address edge.val) potential := by
  have comparison := stationary_block_source_energy_le rule marks field growth growthPositive fieldPositive
    crossing stationary (rule.generation coarse).network
    (fun edge => address ++ generationEdgeAddress rule coarse edge)
    (markedGenerationConfiguration rule marks coarse address opened) fine
    (growth⁻¹ ^ (coarse + fine + 2)) (pow_pos (inv_pos.mpr growthPositive) _)
    (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm vertex))
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
  rw [transport] at comparison
  convert comparison using 1
  · congr 1
    funext edge
    unfold stationaryGenerationResistance
    rw [stationary_block_generation_coefficient growth growthPositive]

end
end IGSIII34.ResistanceLimit
