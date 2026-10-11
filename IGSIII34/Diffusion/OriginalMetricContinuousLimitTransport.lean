import IGSIII34.Diffusion.WholeCadlagIsometricTransport
import IGSIII34.Diffusion.SkorokhodGlobalContinuousLimitCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal PiCountable

/-- The continuity modulus is taken in the original target metric, so the
error is uniform over all true isometric realizations in compact ambients. -/
theorem skorokhodJ1_near_isometric_continuous_uniform
    {Target : Type*} [MetricSpace Target] [CompactSpace Target]
    (limit : C(SkorokhodIntervalTimeCompletion20261011, Target))
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∃ error : ℝ, 0 < error ∧
      ∀ (Ambient : Type*) [MetricSpace Ambient] [CompactSpace Ambient],
      ∀ placement : Target → Ambient, Isometry placement →
      ∀ path : SkorokhodIntervalPathCompletion20261011 Ambient,
      dist path (skorokhodCarrierMapCompletion20261011 placement
        (continuousIntervalPathCompletion20261011 limit)) < error →
      ∀ time, dist (path time) (placement (limit time)) < tolerance := by
  obtain ⟨duration, durationPositive, continuousClose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous limit.continuous) (tolerance / 2) (by positivity)
  let error := min duration (tolerance / 2)
  refine ⟨error, lt_min durationPositive (by positivity), ?_⟩
  intro Ambient _ _ placement isometry path near time
  have nearEDistance : skorokhodJ1EDistCompletion20261011 path
      (skorokhodCarrierMapCompletion20261011 placement (continuousIntervalPathCompletion20261011 limit)) <
      ENNReal.ofReal error := edist_lt_ofReal.mpr near
  obtain ⟨change, changeSmall⟩ := iInf_lt_iff.mp nearEDistance
  have timeSmall : ∀ next, dist (change next) next < error := by
    intro next
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (change next) next) next).trans (le_max_left _ _)).trans_lt changeSmall
  have spatialSmall : ∀ next, dist (path (change next)) (placement (limit next)) < error := by
    intro next
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (path (change next)) (placement (limit next))) next).trans
      (le_max_right _ _)).trans_lt changeSmall
  have spatial := spatialSmall (change.symm time)
  rw [change.apply_symm_apply] at spatial
  have inverseTime : dist (change.symm time) time < duration := by
    have small := timeSmall (change.symm time)
    rw [change.apply_symm_apply, dist_comm] at small
    exact small.trans_le (min_le_left _ _)
  have continuousNear : dist (placement (limit (change.symm time))) (placement (limit time)) < tolerance / 2 := by
    rw [isometry.dist_eq]
    exact continuousClose inverseTime
  have triangle := dist_triangle (path time) (placement (limit (change.symm time))) (placement (limit time))
  have errorBound : error ≤ tolerance / 2 := min_le_right _ _
  linarith

theorem skorokhodGlobal_near_isometric_continuous_uniform
    {Target : Type*} [MetricSpace Target] [CompactSpace Target]
    (limit : ℝ≥0 → Target) (limitContinuous : Continuous limit)
    (horizon : ℝ≥0) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∃ error : ℝ, 0 < error ∧
      ∀ (Ambient : Type*) [MetricSpace Ambient] [CompactSpace Ambient],
      ∀ placement : Target → Ambient, Isometry placement →
      ∀ path : SkorokhodGlobalPathCompletion20261011 Ambient,
      dist path (skorokhodGlobalCarrierMapCompletion20261011 placement ⟨limit⟩) < error →
      ∀ time : ℝ≥0, time ≤ horizon → dist (path time) (placement (limit time)) < tolerance := by
  let count : ℕ := ⌊(horizon : ℝ)⌋₊
  let profile : C(SkorokhodIntervalTimeCompletion20261011, Target) :=
    ⟨fun time => limit ((count+1 : ℝ≥0) * ⟨time.val, time.property.1⟩), limitContinuous.comp (by fun_prop)⟩
  obtain ⟨intervalError, intervalPositive, intervalClose⟩ :=
    skorokhodJ1_near_isometric_continuous_uniform profile tolerance tolerancePositive
  refine ⟨min intervalError (2⁻¹ ^ Encodable.encode count), lt_min intervalPositive (by positivity), ?_⟩
  intro Ambient _ _ placement isometry path near time before
  have coordinateBound :
      dist (skorokhodIntegerProfileCompletion20261011 path count)
        (skorokhodIntegerProfileCompletion20261011
          (skorokhodGlobalCarrierMapCompletion20261011 placement ⟨limit⟩) count) ≤
      dist path (skorokhodGlobalCarrierMapCompletion20261011 placement ⟨limit⟩) :=
    PiCountable.dist_le_dist_pi_of_dist_lt
      (near.trans_le (min_le_right _ _))
  have coordinateNear := coordinateBound.trans_lt (near.trans_le (min_le_left _ _))
  have bound := intervalClose Ambient placement isometry
    (skorokhodIntegerProfileCompletion20261011 path count) coordinateNear
  have countPositive : 0 < (count+1 : ℝ) := by positivity
  have physicalBefore : (time : ℝ) ≤ (count+1 : ℝ) :=
    (NNReal.coe_le_coe.mpr before).trans (Nat.lt_floor_add_one (horizon : ℝ)).le
  let unitTime : SkorokhodIntervalTimeCompletion20261011 :=
    ⟨(time : ℝ) / (count+1 : ℝ),
      ⟨div_nonneg time.property countPositive.le, (div_le_one countPositive).mpr physicalBefore⟩⟩
  have timeIdentity : (count+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩ = time := by
    apply NNReal.eq
    change (count+1 : ℝ) * ((time : ℝ) / (count+1 : ℝ)) = (time : ℝ)
    exact mul_div_cancel₀ _ countPositive.ne'
  have point := bound unitTime
  change dist (path ((count+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩))
    (placement (limit ((count+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩))) < tolerance at point
  rwa [timeIdentity] at point

/-- At a continuous original target, a small whole integer-J1 distance in
any isometric coupling controls genuine J1 on each prescribed horizon. -/
theorem skorokhodGlobal_near_isometric_continuous_horizon
    {Target : Type*} [MetricSpace Target] [CompactSpace Target]
    (limit : ℝ≥0 → Target) (limitContinuous : Continuous limit)
    (horizon : ℝ≥0) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∃ error : ℝ, 0 < error ∧
      ∀ (Ambient : Type*) [MetricSpace Ambient] [CompactSpace Ambient],
      ∀ placement : Target → Ambient, Isometry placement →
      ∀ path : SkorokhodGlobalPathCompletion20261011 Ambient,
      dist path (skorokhodGlobalCarrierMapCompletion20261011 placement ⟨limit⟩) < error →
      dist (skorokhodHorizonRestrictionCompletion20261011 horizon path)
        (skorokhodHorizonRestrictionCompletion20261011 horizon
          (skorokhodGlobalCarrierMapCompletion20261011 placement ⟨limit⟩)) < tolerance := by
  obtain ⟨error, errorPositive, close⟩ := skorokhodGlobal_near_isometric_continuous_uniform
    limit limitContinuous horizon (tolerance / 2) (by positivity)
  refine ⟨error, errorPositive, ?_⟩
  intro Ambient _ _ placement isometry path near
  have bound := close Ambient placement isometry path near
  have edistance : edist (skorokhodHorizonRestrictionCompletion20261011 horizon path)
      (skorokhodHorizonRestrictionCompletion20261011 horizon
        (skorokhodGlobalCarrierMapCompletion20261011 placement ⟨limit⟩)) ≤ ENNReal.ofReal (tolerance / 2) := by
    apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
    apply iSup_le
    intro time
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    apply (bound (horizon * ⟨time.val, time.property.1⟩) ?_).le
    apply NNReal.coe_le_coe.mp
    change (horizon : ℝ) * (time : ℝ) ≤ (horizon : ℝ)
    have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
    have raw := mul_le_mul_of_nonneg_left time.property.2 horizon.property
    rw [realLE] at raw
    rw [mul_one] at raw
    convert raw using 1 <;> rfl
  exact ((edist_le_ofReal (by positivity : 0 ≤ tolerance / 2)).mp edistance).trans_lt (by linarith)

end
end IGSIII34.Diffusion
