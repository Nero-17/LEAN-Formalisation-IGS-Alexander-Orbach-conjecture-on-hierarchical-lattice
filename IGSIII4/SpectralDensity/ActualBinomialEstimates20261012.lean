import IGSIII4.SpectralDensity.ActualMassGrowth20261012
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork Filter Topology

/-- A finite Bernoulli bound in the direction complementary to Bernoulli's inequality. -/
theorem failure_power_times_linear_le_one (failure : ℝ) (nonnegative : 0 ≤ failure)
    (atMostOne : failure ≤ 1) (blocks : ℕ) :
    (1 - failure) ^ blocks * (1 + (blocks : ℝ) * failure) ≤ 1 := by
  induction blocks with
  | zero => simp
  | succ blocks inductionHypothesis =>
    have powerNonnegative : 0 ≤ (1 - failure) ^ blocks := by positivity
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg powerNonnegative (sq_nonneg failure)]

theorem critical_chain_probability_interval (blocks paths interior : ℕ) (probability : ℝ)
    (above : 7 / 10 < probability) (below : probability < 4 / 5)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) :
    25 / 36 < (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks ∧
      (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks < 100 / 119 := by
  have positive : 0 < probability := by linarith
  have belowOne : probability < 1 := by linarith
  rw [actual_critical_equation blocks paths interior probability positive belowOne fixedPoint]
  have denominatorPositive : 0 < probability * (1 + probability) := by positivity
  constructor
  · apply (lt_div_iff₀ denominatorPositive).mpr
    nlinarith
  · apply (div_lt_iff₀ denominatorPositive).mpr
    nlinarith

theorem critical_path_failure_bounds (blocks paths interior : ℕ) (blocksPositive : 0 < blocks)
    (probability : ℝ) (above : 7 / 10 < probability) (below : probability < 4 / 5)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) :
    1 / (8 * (blocks : ℝ)) < (1 - probability ^ (interior + 2)) ^ paths ∧
      (1 - probability ^ (interior + 2)) ^ paths < 1 / (blocks : ℝ) := by
  have positive : 0 < probability := by linarith
  have belowOne : probability ≤ 1 := by linarith
  have pathNonnegative : 0 ≤ probability ^ (interior + 2) := by positivity
  have pathAtMostOne : probability ^ (interior + 2) ≤ 1 := pow_le_one₀ positive.le belowOne
  have failureNonnegative : 0 ≤ (1 - probability ^ (interior + 2)) ^ paths := by positivity
  have failureAtMostOne : (1 - probability ^ (interior + 2)) ^ paths ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr pathAtMostOne) (by linarith)
  have interval := critical_chain_probability_interval blocks paths interior probability above below fixedPoint
  have bernoulliBound := one_sub_power_bound _ failureNonnegative failureAtMostOne blocks
  have reciprocalBound := failure_power_times_linear_le_one _ failureNonnegative failureAtMostOne blocks
  have blocksRealPositive : 0 < (blocks : ℝ) := by exact_mod_cast blocksPositive
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 8 * (blocks : ℝ))).mpr
    nlinarith [interval.2]
  · apply (lt_div_iff₀ blocksRealPositive).mpr
    by_contra failureLarge
    have oneBelow : 1 ≤ (blocks : ℝ) * (1 - probability ^ (interior + 2)) ^ paths := by linarith
    nlinarith [interval.1]

theorem log_one_sub_bounds (value : ℝ) (positive : 0 < value) (atMostHalf : value ≤ 1 / 2) :
    -2 * value ≤ Real.log (1 - value) ∧ Real.log (1 - value) ≤ -value := by
  have complementPositive : 0 < 1 - value := by linarith
  constructor
  · have inverseBound : (1 - value)⁻¹ ≤ 1 + 2 * value := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ complementPositive).mpr
      nlinarith
    exact (by linarith : -2 * value ≤ 1 - (1 - value)⁻¹).trans
      (Real.one_sub_inv_le_log_of_pos complementPositive)
  · simpa using Real.log_le_sub_one_of_pos complementPositive

theorem critical_success_mean_log_bounds (blocks paths interior : ℕ) (blocksPositive : 0 < blocks)
    (probability : ℝ) (above : 7 / 10 < probability) (below : probability < 4 / 5)
    (pathAtMostHalf : probability ^ (interior + 2) ≤ 1 / 2)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) :
    Real.log (blocks : ℝ) / 2 < (paths : ℝ) * probability ^ (interior + 2) ∧
      (paths : ℝ) * probability ^ (interior + 2) < Real.log (8 * (blocks : ℝ)) := by
  have positive : 0 < probability := by linarith
  have pathPositive : 0 < probability ^ (interior + 2) := by positivity
  have complementPositive : 0 < 1 - probability ^ (interior + 2) := by linarith
  have failureBounds := critical_path_failure_bounds blocks paths interior blocksPositive probability above below fixedPoint
  have logs := log_one_sub_bounds _ pathPositive pathAtMostHalf
  have blocksRealPositive : 0 < (blocks : ℝ) := by exact_mod_cast blocksPositive
  have logFailureUpper := Real.log_lt_log (pow_pos complementPositive paths) failureBounds.2
  have logFailureLower := Real.log_lt_log (by positivity : 0 < 1 / (8 * (blocks : ℝ))) failureBounds.1
  rw [Real.log_pow, Real.log_div one_ne_zero blocksRealPositive.ne', Real.log_one, zero_sub] at logFailureUpper
  rw [Real.log_pow, Real.log_div one_ne_zero (by positivity : 8 * (blocks : ℝ) ≠ 0), Real.log_one, zero_sub] at logFailureLower
  have pathsNonnegative : 0 ≤ (paths : ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left logs.1 pathsNonnegative]
  · nlinarith [mul_le_mul_of_nonneg_left logs.2 pathsNonnegative]

theorem appendix_success_mean_bounds_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      (length : ℝ) * Real.log base / 2 < (pathCount length : ℝ) *
          appendixCriticalProbability base length ^ length ∧
        (pathCount length : ℝ) * appendixCriticalProbability base length ^ length <
          ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ) := by
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    eventually_ge_atTop (4 : ℕ)] with length interval lengthLarge
  have lengthAtLeastTwo : 2 ≤ length := by omega
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthAtLeastTwo
  have powerHalf : appendixCriticalProbability base length ^ length ≤ 1 / 2 := by
    calc
      _ ≤ (4 / 5 : ℝ) ^ length := pow_le_pow_left₀ positive.le interval.2.le _
      _ ≤ (4 / 5 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) lengthLarge
      _ ≤ _ := by norm_num
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have logBounds := critical_success_mean_log_bounds (blockCount base length) (pathCount length)
    (length - 2) blocksPositive _ interval.1 interval.2 (by simpa only [Nat.sub_add_cancel lengthAtLeastTwo] using powerHalf) fixedPoint
  simp only [Nat.sub_add_cancel lengthAtLeastTwo] at logBounds
  have blocksLower := (blockCount_bounds base baseAboveOne.le length).1
  have blocksUpper := (blockCount_bounds base baseAboveOne.le length).2
  have blockLogLower := Real.log_le_log (by positivity : 0 < base ^ length) blocksLower
  rw [Real.log_pow] at blockLogLower
  have blockLogUpper := Real.log_le_log (by positivity : 0 < 8 * (blockCount base length : ℝ))
    (mul_le_mul_of_nonneg_left blocksUpper (by norm_num : (0 : ℝ) ≤ 8))
  have logUpperRewrite : Real.log (8 * (2 * base ^ length)) = 4 * Real.log 2 + (length : ℝ) * Real.log base := by
    rw [show 8 * (2 * base ^ length) = (2 : ℝ) ^ 4 * base ^ length by ring,
      Real.log_mul (by norm_num) (by positivity : base ^ length ≠ 0), Real.log_pow, Real.log_pow]
    norm_num
  rw [logUpperRewrite] at blockLogUpper
  have logTwoUpper : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have logBaseUpper : Real.log base ≤ (⌈base⌉₊ : ℝ) - 1 :=
    (Real.log_le_sub_one_of_pos (by linarith : 0 < base)).trans (by linarith [Nat.le_ceil base])
  have lengthRealLarge : 4 ≤ (length : ℝ) := by exact_mod_cast lengthLarge
  constructor
  · linarith [logBounds.1]
  · nlinarith [logBounds.2, mul_le_mul_of_nonneg_left logBaseUpper (Nat.cast_nonneg length)]

end
end IGSIII4.SpectralDensity.ActualFamily
