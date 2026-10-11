import IGSIII34.ResistanceLimit.GenerationBlockTransportCompletion20261011
import IGSIII34.ResistanceLimit.SourceHarmonicFlatnessCompletion20261011

/-! Flatness of an actual generation-block trace minimizer. This proves the
constant-cell property needed to construct topological cutoffs; it does not
postulate that property as part of an energy domain. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

theorem marked_generation_block_source_retained_iff
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (vertex : (rule.generation coarse).network.SubstitutionVertex (rule.generation fine).network) :
    ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex)) ↔
    ((rule.generation coarse).network.substitutedGraph (rule.generation fine).network
      (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened edge))).Reachable
      (Sum.inl (rule.generation coarse).network.source) vertex := by
  have transported := (((rule.generationBlockDecomposition coarse fine).openGraphIso
    (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).reachable_iff
    (u := (rule.generation (coarse + fine + 1)).network.source)
    (v := (rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex))).symm
  change _ ↔ (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    ((rule.generationBlockDecomposition coarse fine).configuration
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened))).Reachable
      ((rule.generationBlockDecomposition coarse fine).vertex (rule.generation (coarse + fine + 1)).network.source)
      ((rule.generationBlockDecomposition coarse fine).vertex
        ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex))) at transported
  rw [marked_generation_block_configuration rule marks coarse fine address opened,
    (rule.generationBlockDecomposition coarse fine).source, Equiv.apply_symm_apply] at transported
  exact transported.trans ((rule.generation coarse).network.substitute_reachable_iff
    (rule.generation fine).network _ (Sum.inl (rule.generation coarse).network.source) vertex)

theorem stationary_generation_block_minimizer_flat_cell
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ)
    (minimizing : sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened))
        (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) address edge.val) potential =
      sourceComponentEnergy (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened))
        (fun edge => stationaryGenerationResistance rule field growth coarse address edge.val)
        (fun vertex => potential (blockOldVertexEmbedding rule coarse fine vertex)))
    (edge : Fin (rule.generation coarse).edges)
    (flatAvailable : markedGenerationConfiguration rule marks coarse address opened edge = true →
      sourceProjection (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened))
        (fun vertex => potential (blockOldVertexEmbedding rule coarse fine vertex))
        ((rule.generation coarse).network.endpoint edge).1 =
      sourceProjection (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened))
        (fun vertex => potential (blockOldVertexEmbedding rule coarse fine vertex))
        ((rule.generation coarse).network.endpoint edge).2)
    (first last : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable first last)
    (firstRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex first))
    (lastRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex last)) :
    potential ((generationBlockCellEmbedding rule coarse fine edge).vertex first) =
      potential ((generationBlockCellEmbedding rule coarse fine edge).vertex last) := by
  have rawMinimizing : sourceComponentEnergy
      (substitutedNetwork (rule.generation coarse).network (rule.generation fine).network
        (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse address opened edge)))
      (fun edge => growth⁻¹ ^ (coarse + fine + 2) * field
        ((address ++ generationEdgeAddress rule coarse edge.1) ++ generationEdgeAddress rule fine edge.2.val))
      (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex))) =
    sourceComponentEnergy (network (rule.generation coarse).network
      ((rule.generation fine).network.coarseConfiguration
        (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse address opened edge))))
      (coarseResistance (rule.generation fine).network
        (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse address opened edge))
        (fun edge => growth⁻¹ ^ (coarse + fine + 2) * field
          ((address ++ generationEdgeAddress rule coarse edge.1) ++ generationEdgeAddress rule fine edge.2.val)))
      (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ (Sum.inl vertex)))) := by
    rw [stationary_block_coarse_resistance rule marks field growth growthPositive fieldPositive crossing stationary
      (fun edge => address ++ generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse address opened) fine
      (growth⁻¹ ^ (coarse + fine + 2)) (pow_pos (inv_pos.mpr growthPositive) _),
      stationary_block_coarsens rule marks crossing (fun edge => address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened) fine]
    have equality := minimizing
    rw [stationary_generation_block_source_energy_transport] at equality
    convert equality using 1
    congr 1
    funext retainedEdge
    unfold stationaryGenerationResistance
    rw [stationary_block_generation_coefficient growth growthPositive]
  apply source_trace_minimizer_flat_cell (rule.generation coarse).network (rule.generation fine).network
    (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse address opened edge))
    (fun edge => growth⁻¹ ^ (coarse + fine + 2) * field
      ((address ++ generationEdgeAddress rule coarse edge.1) ++ generationEdgeAddress rule fine edge.2.val))
    (fun edge => mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _))
    (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex)))
    rawMinimizing edge
  · intro crossingCell
    have retained := (markedGenerationConfiguration_crosses rule marks crossing fine
      (address ++ generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse address opened edge)).symm.trans crossingCell
    have projected := substitution_sourceProjection_old (rule.generation coarse).network (rule.generation fine).network
      (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened edge))
      (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex)))
    rw [stationary_block_coarsens rule marks crossing (fun edge => address ++ generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse address opened) fine] at projected
    exact (congrFun projected _).trans ((flatAvailable retained).trans (congrFun projected _).symm)
  · rwa [generationBlockCells_marked] at reachable
  · rw [substitutedNetwork_graph_eq]
    exact (marked_generation_block_source_retained_iff rule marks coarse fine address opened _).mp firstRetained
  · rw [substitutedNetwork_graph_eq]
    exact (marked_generation_block_source_retained_iff rule marks coarse fine address opened _).mp lastRetained

end
end IGSIII34.ResistanceLimit
