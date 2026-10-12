import IGSIII34.Spectral.ActualVariationalBoundsCompletion

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped Topology

def rationalClockBoundsCompletion {Space : Type*}
    (diagonal : ℕ → Space → ℝ) (resistance : ℝ) (point : Space) : Prop :=
  ∀ tolerance : ℚ, 1 < (tolerance : ℝ) → ∀ᶠ depth : ℕ in atTop,
    1 / (resistance^depth * (tolerance : ℝ)^depth) ≤ diagonal depth point ∧
      diagonal depth point ≤ (tolerance : ℝ)^depth / resistance^depth

theorem rational_clock_bounds_measurable_completion
    {Space : Type*} [MeasurableSpace Space] (diagonal : ℕ → Space → ℝ)
    (resistance : ℝ) (measurable : ∀ depth, Measurable (diagonal depth)) :
    MeasurableSet {point | rationalClockBoundsCompletion diagonal resistance point} := by
  apply Measurable.setOf
  unfold rationalClockBoundsCompletion
  apply Measurable.forall
  intro tolerance
  apply Measurable.imp measurable_const
  simp only [eventually_atTop]
  apply Measurable.exists
  intro threshold
  apply Measurable.forall
  intro depth
  apply Measurable.imp measurable_const
  exact (measurable_const.le' (measurable depth)).and ((measurable depth).le' measurable_const)

theorem rational_clock_bounds_real_slack_completion
    {Space : Type*} (diagonal : ℕ → Space → ℝ)
    (resistance : ℝ) (resistancePositive : 0 < resistance) (point : Space)
    (rational : rationalClockBoundsCompletion diagonal resistance point) :
    ∀ tolerance : ℝ, 1 < tolerance → ∀ᶠ depth : ℕ in atTop,
      1 / (resistance^depth * tolerance^depth) ≤ diagonal depth point ∧
        diagonal depth point ≤ tolerance^depth / resistance^depth := by
  intro tolerance greater
  obtain ⟨ratio, ratioGreater, ratioBelow⟩ := exists_rat_btwn greater
  have ratioPositive := zero_lt_one.trans ratioGreater
  filter_upwards [rational ratio ratioGreater] with depth bound
  have powerComparison := pow_le_pow_left₀ ratioPositive.le ratioBelow.le depth
  constructor
  · exact (one_div_le_one_div_of_le (mul_pos (pow_pos resistancePositive depth) (pow_pos ratioPositive depth))
      (mul_le_mul_of_nonneg_left powerComparison (pow_pos resistancePositive depth).le)).trans bound.1
  · exact bound.2.trans (div_le_div_of_nonneg_right powerComparison (pow_pos resistancePositive depth).le)

theorem rational_clock_bounds_pushforward_completion
    {Boundary Space : Type*} [MeasurableSpace Boundary] [MeasurableSpace Space]
    (boundary : Measure Boundary) (realization : Boundary → Space) (realizationMeasurable : Measurable realization)
    (diagonal : ℕ → Space → ℝ) (resistance : ℝ)
    (measurable : ∀ depth, Measurable (diagonal depth))
    (clockBounds : ∀ᵐ path ∂boundary, rationalClockBoundsCompletion diagonal resistance (realization path)) :
    ∀ᵐ point ∂boundary.map realization, rationalClockBoundsCompletion diagonal resistance point :=
  (ae_map_iff realizationMeasurable.aemeasurable
    (rational_clock_bounds_measurable_completion diagonal resistance measurable)).mpr clockBounds

end
end IGSIII34.Spectral
