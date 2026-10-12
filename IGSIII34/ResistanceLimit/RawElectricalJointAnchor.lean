import IGSIII34.ResistanceLimit.RawElectricalFiniteCluster
import IGSIII34.ResistanceLimit.ActualElectricalLocalMeshCompletion
import IGSIII34.ResistanceLimit.ActualAvailableCellCoverCompletion

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem actual_raw_electrical_joint_anchor
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
    (point : RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive (coarse + fine + 1)) :
    ∃ anchor : RetainedSkeletonVertex (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse),
      dist point (show RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive (coarse + fine + 1) from
        retainedPersistentVertexEmbedding rule (stationaryConfiguration rule marks.val)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
          coarse (coarse + fine + 1) (by omega) anchor) ≤ coefficient * eta ^ (coarse + 1) ∧
      dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (coarse + fine + 1) point)
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks coarse anchor) ≤
          coefficient * eta ^ (coarse + 1) := by
  obtain ⟨edge, child, side, identity, reachable, coarseRetained⟩ :=
    actual_retained_generation_available_cell_cover rule marks.val marks.property.2.1 coarse fine point.val point.property
  let anchor : RetainedSkeletonVertex (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse) :=
    ⟨if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2,
      coarseRetained⟩
  have plantedIdentity :
      (generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side) =
      persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) anchor.val := by
    cases side <;> simp only [anchor, plantedVertex, Bool.false_eq_true, ↓reduceIte,
      generationBlockCellEmbedding_source, generationBlockCellEmbedding_target, blockOldVertexEmbedding_eq_persistent]
  have rawBound := (div_le_div_of_nonneg_right
    ((networkEmbedding_unit_pairResistance_le (generationBlockCellEmbedding rule coarse fine edge)
      (stationaryConfiguration rule marks.val (coarse + fine + 1))
      (plantedVertex (rule.generation fine).network side) child reachable).trans
      (planted_pairResistance_le_radius (rule.generation fine).network
        (generationBlockCells rule coarse fine (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge) side child))
    (pow_pos growthPositive (coarse + fine + 2)).le)
  have cellRadius := radiusBounds (generationEdgeAddress rule coarse edge)
    (stationaryConfiguration rule marks.val coarse edge) fine (by rw [generationEdgeAddress_length]; omega)
  rw [generationEdgeAddress_length] at cellRadius
  rw [stationaryConfiguration, generationBlockCells_marked, List.nil_append] at rawBound
  have normalizedBound := rawBound.trans (by
    simpa only [markedElectricalRadius, stationaryConfiguration, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius)
  have stationaryBound := actual_stationary_local_resistance_mesh_completion rule p positive belowOne fixedPoint
    growth value growthPositive marks fieldLimit eta coefficient start radiusBounds coarse fine beyond edge side child reachable
    (identity ▸ point.property)
  refine ⟨anchor, ?_, ?_⟩
  · rw [dist_comm, rawElectricalFiniteCluster_dist]
    change pairResistance _ (fun _ => 1)
      (persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) anchor.val) point.val /
        growth ^ (coarse + fine + 1 + 1) ≤ _
    rw [← plantedIdentity, identity]
    simpa only [stationaryConfiguration, Nat.add_assoc, show (1 : ℕ) + 1 = 2 from rfl] using normalizedBound
  · have persistent := electricalVertex_persistent rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
      marks.property.2.2 coarse (coarse + fine + 1) (by omega) anchor
    change dist _ (electricalVertex _ _ _ _ _ _ _ _) ≤ _
    rw [persistent]
    change dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks _ point)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks _
        (retainedPersistentVertexEmbedding rule (stationaryConfiguration rule marks.val)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks) coarse (coarse + fine + 1) (by omega) anchor)) ≤ _
    rw [dist_comm, actualStationaryElectricalVertex_distance]
    change pairResistance _ _ (persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) anchor.val) point.val ≤ _
    rw [← plantedIdentity, identity]
    exact stationaryBound

end
end IGSIII34.ResistanceLimit
