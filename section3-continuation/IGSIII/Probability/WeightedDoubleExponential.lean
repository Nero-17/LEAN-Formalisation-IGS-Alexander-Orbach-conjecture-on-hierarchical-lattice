import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

namespace IGSIII.Probability

open Filter
open scoped Topology

theorem weighted_double_exponential_summable (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    {base : ℕ} (baseAtLeastTwo : 2 ≤ base) {ratio : ℝ}
    (ratioNonnegative : 0 ≤ ratio) (ratioBelowOne : ratio < 1) :
    Summable (fun depth : ℕ => growth ^ depth * ratio ^ (base ^ depth)) := by
  have exponentLower (depth : ℕ) : depth + 1 ≤ base ^ depth := by
    induction depth with
    | zero => simp
    | succ depth inductionHypothesis =>
      rw [pow_succ]
      have multiplied := Nat.mul_le_mul_right (base ^ depth) baseAtLeastTwo
      nlinarith
  have powers : Tendsto (fun depth : ℕ => ratio ^ depth) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioBelowOne
  have decaying : Tendsto (fun depth : ℕ => growth * ratio ^ (depth + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, mul_zero] using (powers.comp (tendsto_add_atTop_nat 1)).const_mul growth
  apply summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [decaying.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with depth coefficientBound
  have exponentComparison : base ^ depth + (depth + 1) ≤ base ^ (depth + 1) := by
    have doubled : base ^ depth * 2 ≤ base ^ (depth + 1) := by
      rw [pow_succ]
      exact Nat.mul_le_mul_left _ baseAtLeastTwo
    have lower := exponentLower depth
    omega
  have ratioComparison : ratio ^ (base ^ (depth + 1)) ≤ ratio ^ (base ^ depth) * ratio ^ (depth + 1) :=
    (pow_le_pow_of_le_one ratioNonnegative ratioBelowOne.le exponentComparison).trans_eq (pow_add ratio (base ^ depth) (depth + 1))
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg growthNonnegative _) (pow_nonneg ratioNonnegative _)),
    abs_of_nonneg (mul_nonneg (pow_nonneg growthNonnegative _) (pow_nonneg ratioNonnegative _))]
  calc
    growth ^ (depth + 1) * ratio ^ (base ^ (depth + 1)) ≤
        growth ^ (depth + 1) * (ratio ^ (base ^ depth) * ratio ^ (depth + 1)) :=
      mul_le_mul_of_nonneg_left ratioComparison (pow_nonneg growthNonnegative _)
    _ = (growth * ratio ^ (depth + 1)) * (growth ^ depth * ratio ^ (base ^ depth)) := by
      rw [pow_succ]
      ring
    _ ≤ (1 / 2 : ℝ) * (growth ^ depth * ratio ^ (base ^ depth)) :=
      mul_le_mul_of_nonneg_right coefficientBound
        (mul_nonneg (pow_nonneg growthNonnegative _) (pow_nonneg ratioNonnegative _))

end IGSIII.Probability
