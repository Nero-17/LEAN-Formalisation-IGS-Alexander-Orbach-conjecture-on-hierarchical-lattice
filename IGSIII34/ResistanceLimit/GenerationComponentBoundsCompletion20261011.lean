import IGSIII34.ResistanceLimit.GenerationHarmonicBoundsCompletion20261011
import IGSIII34.ResistanceLimit.SourceComponentDeviationCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

theorem stationary_generation_block_minimizer_component_deviation_completion20261011
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
    (edge : Fin (rule.generation coarse).edges) (reference error : ℝ)
    (vertex : Fin (rule.generation fine).vertices)
    (boundaryDeviation : ∀ terminal : Fin (rule.generation fine).vertices,
      terminal = (rule.generation fine).network.source ∨ terminal = (rule.generation fine).network.target →
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable terminal vertex →
      ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
        (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex terminal) →
      |potential ((generationBlockCellEmbedding rule coarse fine edge).vertex terminal) - reference| ≤ error)
    (available : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
        (rule.generation fine).network.source vertex ∨
      ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
        (rule.generation fine).network.target vertex)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex)) :
    |potential ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) - reference| ≤ error := by
  refine source_trace_minimizer_component_deviation (rule.generation coarse).network (rule.generation fine).network
    (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse address opened edge))
    (fun edge => growth⁻¹ ^ (coarse + fine + 2) * field
      ((address ++ generationEdgeAddress rule coarse edge.1) ++ generationEdgeAddress rule fine edge.2.val))
    (fun edge => mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _))
    (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ vertex)))
    (stationary_generation_block_minimum_transport rule marks field growth growthPositive fieldPositive crossing stationary
      coarse fine address opened potential minimizing) edge reference error vertex ?_ ?_ ?_
  · intro terminal boundary terminalReachable terminalRetained
    apply boundaryDeviation terminal boundary
    · simpa only [generationBlockCells_marked] using terminalReachable
    ·
      apply (marked_generation_block_source_retained_iff rule marks coarse fine address opened _).mpr
      rwa [substitutedNetwork_graph_eq] at terminalRetained
  · simpa only [generationBlockCells_marked] using available
  · rw [substitutedNetwork_graph_eq]
    exact (marked_generation_block_source_retained_iff rule marks coarse fine address opened _).mp retained

end
end IGSIII34.ResistanceLimit

