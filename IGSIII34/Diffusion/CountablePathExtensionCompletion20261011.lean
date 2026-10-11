import IGSIII34.Diffusion.CountablePathContinuityCompletion20261011
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def countableTimeLocalUniformContinuityCompletion20261011 (times : ℕ → ℝ≥0) (path : ℕ → Space) : Prop :=
  ∀ horizon : ℕ, ∀ tolerance : ℝ, 0 < tolerance →
    ∃ duration : ℝ, 0 < duration ∧ ∀ first last : ℕ,
      (times first : ℝ) ≤ horizon → (times last : ℝ) ≤ horizon →
      dist (times first) (times last) < duration → dist (path first) (path last) < tolerance

def countableTimeRangeFunctionCompletion20261011 (times : ℕ → ℝ≥0) (path : ℕ → Space) (time : ℝ≥0) : Space := by
  classical
  exact if member : time ∈ range times then path (Classical.choose member) else path 0

def countableTimeContinuousExtensionCompletion20261011 (times : ℕ → ℝ≥0) (path : ℕ → Space) : ℝ≥0 → Space :=
  extendFrom (range times) (countableTimeRangeFunctionCompletion20261011 times path)

theorem countableTimeLocalUniform_timestamp_consistency_completion20261011
    (times : ℕ → ℝ≥0) (path : ℕ → Space)
    (regular : countableTimeLocalUniformContinuityCompletion20261011 times path)
    (first last : ℕ) (equal : times first = times last) : path first = path last := by
  obtain ⟨horizon, bounded⟩ := exists_nat_ge (times first : ℝ)
  have small : ∀ tolerance : ℝ, 0 < tolerance → dist (path first) (path last) < tolerance := by
    intro tolerance positive
    obtain ⟨duration, durationPositive, close⟩ := regular horizon tolerance positive
    exact close first last bounded (by simpa only [← equal] using bounded) (by rw [equal, dist_self]; exact durationPositive)
  apply dist_le_zero.mp
  apply le_of_forall_pos_le_add
  intro tolerance positive
  simpa only [zero_add] using (small tolerance positive).le

theorem countableTimeRangeFunction_at_timestamp_completion20261011
    (times : ℕ → ℝ≥0) (path : ℕ → Space)
    (regular : countableTimeLocalUniformContinuityCompletion20261011 times path) (coordinate : ℕ) :
    countableTimeRangeFunctionCompletion20261011 times path (times coordinate) = path coordinate := by
  have member : times coordinate ∈ range times := ⟨coordinate, rfl⟩
  rw [countableTimeRangeFunctionCompletion20261011, dif_pos member]
  exact countableTimeLocalUniform_timestamp_consistency_completion20261011 times path regular
    (Classical.choose member) coordinate (Classical.choose_spec member)

theorem countableTimeRangeFunction_cauchy_at_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (path : ℕ → Space)
    (regular : countableTimeLocalUniformContinuityCompletion20261011 times path) (time : ℝ≥0) :
    Cauchy (Filter.map (countableTimeRangeFunctionCompletion20261011 times path) (𝓝[range times] time)) := by
  classical
  letI : NeBot (𝓝[range times] time) := mem_closure_iff_nhdsWithin_neBot.mp (dense time)
  refine Metric.cauchy_iff.mpr ⟨by infer_instance, ?_⟩
  intro tolerance positive
  obtain ⟨horizon, bounded⟩ := exists_nat_gt (time : ℝ)
  obtain ⟨duration, durationPositive, close⟩ := regular horizon tolerance positive
  let neighborhood := range times ∩ (Iio (horizon : ℝ≥0) ∩ Metric.ball time (duration / 2))
  have neighborhoodMem : neighborhood ∈ 𝓝[range times] time := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show time < (horizon : ℝ≥0) by exact_mod_cast bounded)),
      nhdsWithin_le_nhds (Metric.ball_mem_nhds time (show 0 < duration / 2 by linarith))] with point member before near
    exact ⟨member, before, near⟩
  refine ⟨(countableTimeRangeFunctionCompletion20261011 times path) '' neighborhood,
    Filter.image_mem_map neighborhoodMem, ?_⟩
  rintro first ⟨firstTime, firstMember, rfl⟩ last ⟨lastTime, lastMember, rfl⟩
  obtain ⟨firstCoordinate, firstEq⟩ := firstMember.1
  obtain ⟨lastCoordinate, lastEq⟩ := lastMember.1
  rw [← firstEq, ← lastEq, countableTimeRangeFunction_at_timestamp_completion20261011 times path regular,
    countableTimeRangeFunction_at_timestamp_completion20261011 times path regular]
  apply close firstCoordinate lastCoordinate
  · rw [firstEq]
    exact_mod_cast firstMember.2.1.le
  · rw [lastEq]
    exact_mod_cast lastMember.2.1.le
  · rw [firstEq, lastEq]
    have triangle := dist_triangle firstTime time lastTime
    have firstNear := firstMember.2.2
    have lastNear := lastMember.2.2
    change dist firstTime time < duration / 2 at firstNear
    change dist lastTime time < duration / 2 at lastNear
    rw [dist_comm time lastTime] at triangle
    linarith

theorem countableTimeRangeFunction_continuousOn_completion20261011
    (times : ℕ → ℝ≥0) (path : ℕ → Space)
    (regular : countableTimeLocalUniformContinuityCompletion20261011 times path) :
    ContinuousOn (countableTimeRangeFunctionCompletion20261011 times path) (range times) := by
  intro time member
  obtain ⟨coordinate, coordinateEq⟩ := member
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  obtain ⟨horizon, bounded⟩ := exists_nat_gt (time : ℝ)
  obtain ⟨duration, durationPositive, close⟩ := regular horizon tolerance positive
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show time < (horizon : ℝ≥0) by exact_mod_cast bounded)),
    nhdsWithin_le_nhds (Metric.ball_mem_nhds time durationPositive)] with other member before near
  obtain ⟨otherCoordinate, otherEq⟩ := member
  rw [← otherEq, ← coordinateEq, countableTimeRangeFunction_at_timestamp_completion20261011 times path regular,
    countableTimeRangeFunction_at_timestamp_completion20261011 times path regular]
  apply close otherCoordinate coordinate
  · rw [otherEq]
    exact_mod_cast before.le
  · rw [coordinateEq]
    exact bounded.le
  · change dist other time < duration at near
    simpa only [otherEq, coordinateEq] using near

/-- A locally uniformly continuous countable sample has a canonical
continuous extension to every nonnegative real time, even when timestamp
enumeration has repetitions. No extension is assumed. -/
theorem countableTimeContinuousExtension_properties_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (path : ℕ → Space)
    (regular : countableTimeLocalUniformContinuityCompletion20261011 times path) :
    Continuous (countableTimeContinuousExtensionCompletion20261011 times path) ∧
      ∀ coordinate, countableTimeContinuousExtensionCompletion20261011 times path (times coordinate) = path coordinate := by
  have limits : ∀ time : ℝ≥0, ∃ point, Tendsto (countableTimeRangeFunctionCompletion20261011 times path)
      (𝓝[range times] time) (𝓝 point) := fun time => CompleteSpace.complete
        (countableTimeRangeFunction_cauchy_at_completion20261011 times dense path regular time)
  refine ⟨continuous_extendFrom dense limits, ?_⟩
  intro coordinate
  exact (extendFrom_extends (countableTimeRangeFunction_continuousOn_completion20261011 times path regular)
    (times coordinate) ⟨coordinate, rfl⟩).trans
      (countableTimeRangeFunction_at_timestamp_completion20261011 times path regular coordinate)

theorem countableTimeContinuousExtension_unique_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (path : ℕ → Space)
    (regular : countableTimeLocalUniformContinuityCompletion20261011 times path)
    (other : ℝ≥0 → Space) (continuous : Continuous other) (agrees : ∀ coordinate, other (times coordinate) = path coordinate) :
    countableTimeContinuousExtensionCompletion20261011 times path = other := by
  apply dense.equalizer ((countableTimeContinuousExtension_properties_completion20261011 times dense path regular).1) continuous
  funext coordinate
  exact ((countableTimeContinuousExtension_properties_completion20261011 times dense path regular).2 coordinate).trans (agrees coordinate).symm

end
end IGSIII34.Diffusion
