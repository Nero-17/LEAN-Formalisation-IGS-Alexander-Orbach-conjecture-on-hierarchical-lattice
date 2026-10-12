import IGSIII34.Diffusion.OriginalEnergyMeshOscillationCompletion
import IGSIII34.ResistanceLimit.ActualBlockElectricalCompletion

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

/-- The original full-cluster block resistance is controlled by the actual
marked electrical radius of that block, with the paper's exact level shift. -/
theorem original_block_normalized_resistance_bound_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (growth eta coefficient : ℝ) (start : ℕ) (growthPositive : 0 < growth)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (coarse fine : ℕ) (edge : Fin (rule.generation coarse).edges) (side : Bool)
    (vertex : Fin (rule.generation fine).vertices) (beyond : start ≤ coarse)
    (reachable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).Reachable
      (plantedVertex (rule.generation fine).network side) vertex) :
    pairResistance (network (rule.generation (coarse + fine + 1)).network
      (stationaryConfiguration rule marks (coarse + fine + 1))) (fun _ => 1)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
      ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) /
      growth ^ (coarse + fine + 2) ≤ coefficient * eta ^ (coarse + 1) := by
  have embeddingBound := networkEmbedding_unit_pairResistance_le (generationBlockCellEmbedding rule coarse fine edge)
    (stationaryConfiguration rule marks (coarse + fine + 1)) (plantedVertex (rule.generation fine).network side) vertex reachable
  have normalized := div_le_div_of_nonneg_right
    (embeddingBound.trans (planted_pairResistance_le_radius (rule.generation fine).network
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge) side vertex))
    (pow_pos growthPositive (coarse + fine + 2)).le
  have cellRadius := radiusBound (generationEdgeAddress rule coarse edge)
    (stationaryConfiguration rule marks coarse edge) fine (by rw [generationEdgeAddress_length]; omega)
  rw [generationEdgeAddress_length] at cellRadius
  rw [stationaryConfiguration, generationBlockCells_marked, List.nil_append] at normalized
  exact normalized.trans (by
    simpa only [markedElectricalRadius, stationaryConfiguration, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius)

/-- Every genuine original finite potential of bounded normalized energy
has a uniformly small amplitude in each available coarse-cell component.
This includes each side of a noncrossing cell separately. -/
theorem original_block_energy_oscillation_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (growth eta coefficient : ℝ) (start : ℕ) (growthPositive : 0 < growth)
    (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (coarse fine : ℕ) (edge : Fin (rule.generation coarse).edges) (side : Bool)
    (vertex : Fin (rule.generation fine).vertices) (beyond : start ≤ coarse)
    (reachable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).Reachable
      (plantedVertex (rule.generation fine).network side) vertex)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (stationaryConfiguration rule marks (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex))
    (potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ) (bound : ℝ)
    (energyBound : growth ^ (coarse + fine + 2) * sourceComponentEnergy
      (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
      (fun _ => 1) potential ≤ bound) :
    (potential ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side)) -
      potential ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex)) ^ 2 ≤
      coefficient * eta ^ (coarse + 1) * bound := by
  have mapped := reachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom
    (stationaryConfiguration rule marks (coarse + fine + 1)))
  have terminalRetained := retained.trans (by
    simpa only [generationBlockCellEmbedding_openGraphHom_apply] using mapped.symm)
  have terminalReach : (network (rule.generation (coarse + fine + 1)).network
      (stationaryConfiguration rule marks (coarse + fine + 1))).graph.Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side)) := by
    rwa [graph_eq_openGraph]
  have vertexReach : (network (rule.generation (coarse + fine + 1)).network
      (stationaryConfiguration rule marks (coarse + fine + 1))).graph.Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) := by rwa [graph_eq_openGraph]
  have oscillation := sourceComponentEnergy_resistance_bound
    (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
    (fun _ => 1) (fun _ => zero_lt_one) potential terminalReach vertexReach
  have energyNonnegative := sourceComponentEnergy_nonnegative
    (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
    (fun _ => 1) (fun _ => zero_lt_one) potential
  have resistanceBound := original_block_normalized_resistance_bound_completion rule marks growth eta coefficient start
    growthPositive radiusBound coarse fine edge side vertex beyond reachable
  have productBound := mul_le_mul_of_nonneg_right resistanceBound
    (mul_nonneg (pow_pos growthPositive (coarse + fine + 2)).le energyNonnegative)
  have cancellation :
      pairResistance (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
        (fun _ => 1) ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) / growth ^ (coarse + fine + 2) *
        (growth ^ (coarse + fine + 2) * sourceComponentEnergy
          (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
          (fun _ => 1) potential) =
      pairResistance (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
        (fun _ => 1) ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) * sourceComponentEnergy
          (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
          (fun _ => 1) potential := by field_simp [growthPositive.ne']
  rw [cancellation] at productBound
  exact oscillation.trans (productBound.trans (mul_le_mul_of_nonneg_left energyBound
    (mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _))))

end
end IGSIII34.Diffusion
