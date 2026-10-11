import IGSIII34.ResistanceLimit.ActualBlockElectricalCompletion20261011
import IGSIII34.ResistanceLimit.ActualElectricalMassCompletion20261011

/-! True stationary local resistance mesh, derived by passing the actual
unit-edge component-radius bounds to the actual stationary resistance limit. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem actual_stationary_local_resistance_mesh_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (coarse fine : ℕ) (beyond : start ≤ coarse)
    (edge : Fin (rule.generation coarse).edges) (side : Bool)
    (vertex : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).Reachable
      (plantedVertex (rule.generation fine).network side) vertex)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (stationaryConfiguration rule marks.val (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex)) :
    pairResistance (network (rule.generation (coarse + fine + 1)).network
      (stationaryConfiguration rule marks.val (coarse + fine + 1)))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (coarse + fine + 1))
      ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
      ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) ≤ coefficient * eta ^ (coarse + 1) := by
  have anchorRetained := retained.trans ((reachable.map
    ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom
      (stationaryConfiguration rule marks.val (coarse + fine + 1)))).symm)
  have bound := actualElectricalVertex_dist_block_le rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit coarse fine edge side vertex reachable anchorRetained retained (coefficient * eta ^ (coarse + 1)) (by
      intro host point localReachable
      have embeddingBound := networkEmbedding_unit_pairResistance_le (generationBlockCellEmbedding rule coarse host edge)
        (stationaryConfiguration rule marks.val (coarse + host + 1)) (plantedVertex (rule.generation host).network side) point localReachable
      have normalized := div_le_div_of_nonneg_right
        (embeddingBound.trans (planted_pairResistance_le_radius (rule.generation host).network
          (generationBlockCells rule coarse host (stationaryConfiguration rule marks.val (coarse + host + 1)) edge) side point))
        (pow_pos growthPositive (coarse + host + 2)).le
      have cellRadius := radiusBounds (generationEdgeAddress rule coarse edge)
        (stationaryConfiguration rule marks.val coarse edge) host (by rw [generationEdgeAddress_length]; omega)
      rw [generationEdgeAddress_length] at cellRadius
      rw [stationaryConfiguration, generationBlockCells_marked, List.nil_append] at normalized
      exact normalized.trans (by simpa only [markedElectricalRadius, stationaryConfiguration,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius))
  rwa [actualStationaryElectricalVertex_distance] at bound

end
end IGSIII34.ResistanceLimit
