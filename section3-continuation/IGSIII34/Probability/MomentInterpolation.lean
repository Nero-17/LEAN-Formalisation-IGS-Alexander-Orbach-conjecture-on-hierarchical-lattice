import IGSIII34.Probability.MomentConstraints
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

theorem lintegral_meanOne_moment_interpolation (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1)
    {power order : ℕ} (powerAtLeastTwo : 2 ≤ power)
    (orderPositive : 1 ≤ order) (orderBound : order ≤ power) :
    (∫⁻ value, (value : ℝ≥0∞) ^ order ∂(law : Measure ℝ≥0)) ≤
      (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ^
        (((order : ℝ) - 1) / ((power : ℝ) - 1)) := by
  have denominatorPositive : 0 < (power : ℝ) - 1 := by
    have : (2 : ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have fractionNonnegative : 0 ≤ ((order : ℝ) - 1) / ((power : ℝ) - 1) := by
    apply div_nonneg _ denominatorPositive.le
    have : (1 : ℝ) ≤ order := by exact_mod_cast orderPositive
    linarith
  have fractionAtMostOne : ((order : ℝ) - 1) / ((power : ℝ) - 1) ≤ 1 := by
    apply (div_le_iff₀ denominatorPositive).mpr
    have : (order : ℝ) ≤ power := by exact_mod_cast orderBound
    linarith
  have identity : (power : ℝ) * (((order : ℝ) - 1) / ((power : ℝ) - 1)) +
      (1 - (((order : ℝ) - 1) / ((power : ℝ) - 1))) = order := by
    field_simp [denominatorPositive.ne']
    ring
  have pointwise (value : ℝ≥0) :
      ((value : ℝ≥0∞) ^ power) ^ (((order : ℝ) - 1) / ((power : ℝ) - 1)) *
        (value : ℝ≥0∞) ^ (1 - (((order : ℝ) - 1) / ((power : ℝ) - 1))) =
        (value : ℝ≥0∞) ^ order := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _
      (mul_nonneg (Nat.cast_nonneg _) fractionNonnegative) (sub_nonneg.mpr fractionAtMostOne),
      identity, ENNReal.rpow_natCast]
  have holder := ENNReal.lintegral_mul_norm_pow_le
    (f := fun value : ℝ≥0 => (value : ℝ≥0∞) ^ power)
    (g := fun value : ℝ≥0 => (value : ℝ≥0∞))
    (μ := (law : Measure ℝ≥0))
    (measurable_id.coe_nnreal_ennreal.pow_const power).aemeasurable
    measurable_id.coe_nnreal_ennreal.aemeasurable fractionNonnegative
    (sub_nonneg.mpr fractionAtMostOne) (by ring)
  simpa only [pointwise, meanOne, ENNReal.one_rpow, mul_one] using holder

end
end IGSIII34.Probability
