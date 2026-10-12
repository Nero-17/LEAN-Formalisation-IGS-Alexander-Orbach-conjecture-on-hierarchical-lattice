import IGSIII34.ResistanceLimit.RawElectricalJointAnchor
import IGSIII34.Topology.JointAnchorDistortionCompletion

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem actual_raw_electrical_birth_uniform_distortion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ first last : RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth,
      |dist first last - dist
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth first)
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth last)| < tolerance := by
  have meshVanish : Tendsto (fun coarse : ℕ => coefficient * eta ^ (coarse + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp
        (tendsto_add_atTop_nat 1)).const_mul coefficient)
  obtain ⟨coarse, beyond, meshSmall⟩ :=
    ((eventually_ge_atTop start).and
      (meshVanish.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < tolerance / 8)))).exists
  have anchorSmall : ∀ᶠ depth in atTop, ∀ first last :
      RetainedSkeletonVertex (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse),
      |persistentNormalizedResistance rule (stationaryConfiguration rule marks.val) growth coarse first.val last.val depth -
        dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks coarse first)
          (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks coarse last)| < tolerance / 2 := by
    apply Filter.eventually_all.mpr
    intro first
    apply Filter.eventually_all.mpr
    intro last
    have convergence := actual_persistent_skeleton_resistances_tendsto rule marks.val marks.property.2.1 growth growthPositive
      (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
      (fun address => (marks.property.1 address).le) fieldLimit coarse (first.property.symm.trans last.property)
    have close := Metric.tendsto_nhds.mp convergence (tolerance / 2) (by positivity)
    simp only [actualStationaryElectricalVertex_distance]
    unfold stationaryResistance
    simpa only [Real.dist_eq] using close
  obtain ⟨threshold, largeBounds⟩ := eventually_atTop.mp anchorSmall
  refine eventually_atTop.mpr ⟨max threshold (coarse + 1), ?_⟩
  intro depth large first last
  obtain ⟨fine, depthIdentity⟩ : ∃ fine : ℕ, depth = coarse + fine + 1 :=
    ⟨depth - coarse - 1, by omega⟩
  subst depth
  have anchorBounds := largeBounds (coarse + fine + 1) (by omega)
  have fullBound := IGSIII34.Topology.joint_anchor_projection_distortion_completion
    (fun anchor => show RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive (coarse + fine + 1) from
      retainedPersistentVertexEmbedding rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks) coarse (coarse + fine + 1) (by omega) anchor)
    (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks coarse)
    (fun point : RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive (coarse + fine + 1) =>
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (coarse + fine + 1) point)
    (coefficient * eta ^ (coarse + 1)) (coefficient * eta ^ (coarse + 1)) (tolerance / 2)
    (actual_raw_electrical_joint_anchor rule p positive belowOne fixedPoint growth value growthPositive marks fieldLimit
      eta coefficient start radiusBounds coarse fine beyond)
    (fun first last => by
      have small := (anchorBounds first last).le
      simpa only [rawElectricalFiniteCluster_dist, retainedPersistentVertexEmbedding_val, persistentNormalizedResistance,
        dif_pos (by omega : coarse ≤ coarse + fine + 1)] using small)
    first last
  exact fullBound.trans_lt (by linarith)

end
end IGSIII34.ResistanceLimit
