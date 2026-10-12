import IGSIII4.SpectralDensity.CeilingGrowth20261012
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology

theorem one_sub_power_bound (value : ℝ) (nonnegative : 0 ≤ value) (atMostOne : value ≤ 1)
    (power : ℕ) : 1 - (1 - value) ^ power ≤ (power : ℝ) * value := by
  induction power with
  | zero => simp
  | succ power inductionHypothesis =>
    have powerAtMostOne := pow_le_one₀ (n := power) (sub_nonneg.mpr atMostOne)
      (show 1 - value ≤ 1 by linarith)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem unit_interval_power_le_self (value : ℝ) (nonnegative : 0 ≤ value) (atMostOne : value ≤ 1)
    (power : ℕ) (positivePower : 1 ≤ power) : value ^ power ≤ value := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : power ≠ 0)
  rw [pow_succ]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ nonnegative atMostOne) nonnegative).trans_eq (one_mul value)

theorem endpoint_lower_test_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ depth : ℕ in atTop,
      (1 - (1 - (7 / 10 : ℝ) ^ depth) ^ pathCount depth) ^ blockCount base depth < 100 / 119 := by
  have vanishing := (tendsto_self_mul_const_pow_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 14 / 15) (by norm_num : (14 / 15 : ℝ) < 1)).const_mul 2
  have small : ∀ᶠ depth : ℕ in atTop,
      2 * ((depth : ℝ) * (14 / 15 : ℝ) ^ depth) < 100 / 119 := by
    exact vanishing.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [small, eventually_ge_atTop (1 : ℕ)] with depth small depthPositive
  have probabilityPowerNonnegative : 0 ≤ (7 / 10 : ℝ) ^ depth := by positivity
  have probabilityPowerAtMostOne : (7 / 10 : ℝ) ^ depth ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have failureNonnegative : 0 ≤ (1 - (7 / 10 : ℝ) ^ depth) ^ pathCount depth := by positivity
  have failureAtMostOne : (1 - (7 / 10 : ℝ) ^ depth) ^ pathCount depth ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  have blocksPositive : 1 ≤ blockCount base depth := by
    have bound := (blockCount_bounds base baseAboveOne.le depth).1
    have oneBelowPower := one_le_pow₀ baseAboveOne.le (n := depth)
    exact_mod_cast (show (1 : ℝ) ≤ (blockCount base depth : ℝ) from oneBelowPower.trans bound)
  have chainBound := unit_interval_power_le_self
    (1 - (1 - (7 / 10 : ℝ) ^ depth) ^ pathCount depth)
    (by linarith) (by linarith) (blockCount base depth) blocksPositive
  have blockBound := one_sub_power_bound _ probabilityPowerNonnegative probabilityPowerAtMostOne (pathCount depth)
  have expectedPathsBound := mul_le_mul_of_nonneg_right
    (pathCount_bounds depth depthPositive).2 probabilityPowerNonnegative
  have expectedPathsIdentity :
      2 * ((depth : ℝ) * (4 / 3 : ℝ) ^ depth) * (7 / 10 : ℝ) ^ depth =
        2 * ((depth : ℝ) * (14 / 15 : ℝ) ^ depth) := by
    rw [show (14 / 15 : ℝ) = (4 / 3) * (7 / 10) by norm_num, mul_pow]
    ring
  rw [expectedPathsIdentity] at expectedPathsBound
  exact (chainBound.trans (blockBound.trans expectedPathsBound)).trans_lt small

theorem failure_probability_le_exp (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMostOne : probability ≤ 1) (length paths : ℕ) :
    (1 - probability ^ length) ^ paths ≤ Real.exp (-((paths : ℝ) * probability ^ length)) := by
  have powerAtMostOne := pow_le_one₀ (n := length) nonnegative atMostOne
  have exponentialBound : 1 - probability ^ length ≤ Real.exp (-(probability ^ length)) := by
    have bound := Real.add_one_le_exp (-(probability ^ length))
    linarith
  have bound := pow_le_pow_left₀ (sub_nonneg.mpr powerAtMostOne) exponentialBound paths
  rw [← Real.exp_nat_mul] at bound
  convert bound using 1 <;> congr 1 <;> ring

theorem endpoint_upper_test_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ depth : ℕ in atTop,
      25 / 36 < (1 - (1 - (4 / 5 : ℝ) ^ depth) ^ pathCount depth) ^ blockCount base depth := by
  have largePower : ∀ᶠ depth : ℕ in atTop,
      Real.log base + 1 ≤ (16 / 15 : ℝ) ^ depth :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 16 / 15)).eventually
      (eventually_ge_atTop _)
  have vanishing : Tendsto (fun depth : ℕ => 2 * Real.exp (-(depth : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    have limit := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-1)).le
      (by rw [Real.exp_lt_one_iff]; norm_num : Real.exp (-1) < 1)).const_mul 2
    simpa only [← Real.exp_nat_mul, mul_neg, mul_one, mul_zero] using limit
  have small : ∀ᶠ depth : ℕ in atTop, 2 * Real.exp (-(depth : ℝ)) < 11 / 36 :=
    vanishing.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [largePower, small, eventually_ge_atTop (1 : ℕ)] with depth largePower small depthPositive
  have depthNonnegative : 0 ≤ (depth : ℝ) := Nat.cast_nonneg _
  have expectedPathsLower := mul_le_mul_of_nonneg_right (pathCount_bounds depth depthPositive).1
    (by positivity : 0 ≤ (4 / 5 : ℝ) ^ depth)
  have expectedPathsIdentity :
      (depth : ℝ) * (4 / 3 : ℝ) ^ depth * (4 / 5 : ℝ) ^ depth =
        (depth : ℝ) * (16 / 15 : ℝ) ^ depth := by
    rw [show (16 / 15 : ℝ) = (4 / 3) * (4 / 5) by norm_num, mul_pow]
    ring
  rw [expectedPathsIdentity] at expectedPathsLower
  have probabilityPowerNonnegative : 0 ≤ (4 / 5 : ℝ) ^ depth := by positivity
  have probabilityPowerAtMostOne : (4 / 5 : ℝ) ^ depth ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have failureBaseNonnegative : 0 ≤ 1 - (4 / 5 : ℝ) ^ depth := sub_nonneg.mpr probabilityPowerAtMostOne
  have exponentBound :
      (depth : ℝ) * Real.log base - (pathCount depth : ℝ) * (4 / 5 : ℝ) ^ depth ≤ -(depth : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left largePower depthNonnegative]
  have weightedFailureBound :
      (blockCount base depth : ℝ) * (1 - (4 / 5 : ℝ) ^ depth) ^ pathCount depth ≤
        2 * Real.exp (-(depth : ℝ)) := by
    have productBound := mul_le_mul (blockCount_bounds base baseAboveOne.le depth).2
      (failure_probability_le_exp (4 / 5) (by norm_num) (by norm_num) depth (pathCount depth))
      (pow_nonneg failureBaseNonnegative _) (by positivity : 0 ≤ 2 * base ^ depth)
    calc
      _ ≤ 2 * base ^ depth * Real.exp (-((pathCount depth : ℝ) * (4 / 5 : ℝ) ^ depth)) := productBound
      _ = 2 * Real.exp ((depth : ℝ) * Real.log base -
          (pathCount depth : ℝ) * (4 / 5 : ℝ) ^ depth) := by
        rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by linarith : 0 < base), Real.exp_neg]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponentBound) (by norm_num)
  have failureNonnegative : 0 ≤ (1 - (4 / 5 : ℝ) ^ depth) ^ pathCount depth := pow_nonneg failureBaseNonnegative _
  have failureAtMostOne : (1 - (4 / 5 : ℝ) ^ depth) ^ pathCount depth ≤ 1 :=
    pow_le_one₀ failureBaseNonnegative (by linarith)
  have chainFailureBound := one_sub_power_bound _ failureNonnegative failureAtMostOne (blockCount base depth)
  linarith

end
end IGSIII4.SpectralDensity
