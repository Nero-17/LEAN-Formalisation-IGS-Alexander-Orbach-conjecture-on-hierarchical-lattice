import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology

theorem eigenEuler_discrete_error_completion20261011
    (values : ℕ → ℝ) (ratio error : ℝ) (ratioNonnegative : 0 ≤ ratio)
    (ratioAtMostOne : ratio ≤ 1) (errorNonnegative : 0 ≤ error)
    (recursion : ∀ step, |values (step + 1) - ratio * values step| ≤ error)
    (steps : ℕ) : |values steps - ratio ^ steps * values 0| ≤ (steps : ℝ) * error := by
  induction steps with
  | zero => simp
  | succ steps previous =>
    have split : values (steps + 1) - ratio ^ (steps + 1) * values 0 =
        (values (steps + 1) - ratio * values steps) +
          ratio * (values steps - ratio ^ steps * values 0) := by
      rw [pow_succ]
      ring
    rw [split]
    calc
      _ ≤ |values (steps + 1) - ratio * values steps| +
          |ratio * (values steps - ratio ^ steps * values 0)| := abs_add_le _ _
      _ ≤ error + ratio * ((steps : ℝ) * error) := by
        rw [abs_mul, abs_of_nonneg ratioNonnegative]
        exact add_le_add (recursion steps) (mul_le_mul_of_nonneg_left previous ratioNonnegative)
      _ ≤ ((steps + 1 : ℕ) : ℝ) * error := by
        rw [Nat.cast_add, Nat.cast_one]
        have := mul_le_mul_of_nonneg_right ratioAtMostOne (mul_nonneg (Nat.cast_nonneg steps) errorNonnegative)
        nlinarith

theorem eigenEuler_log_scale_completion20261011
    (scales : ℕ → ℝ) (diverges : Tendsto scales atTop atTop)
    (eigenvalue : ℝ) (eigenvaluePositive : 0 < eigenvalue) :
    Tendsto (fun depth => scales depth * Real.log (1 - eigenvalue / scales depth)) atTop (𝓝 (-eigenvalue)) := by
  have increments : Tendsto (fun depth => -eigenvalue / scales depth) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨diverges.const_div_atTop (-eigenvalue), ?_⟩
    filter_upwards [diverges.eventually (eventually_gt_atTop 0)] with depth positive
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      div_ne_zero (neg_ne_zero.mpr eigenvaluePositive.ne') positive.ne'
  have logarithmicSlope : Tendsto (fun increment : ℝ => increment⁻¹ * Real.log (1 + increment))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa only [one_div, inv_one, Real.log_one, sub_zero, smul_eq_mul] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero
  have limit := (tendsto_const_nhds (x := -eigenvalue)).mul (logarithmicSlope.comp increments)
  apply Tendsto.congr' _ (by simpa only [mul_one] using limit)
  filter_upwards [diverges.eventually (eventually_gt_atTop 0)] with depth positive
  dsimp
  have argument : 1 + -eigenvalue / scales depth = 1 - eigenvalue / scales depth := by ring
  rw [argument]
  field_simp [positive.ne', eigenvaluePositive.ne']

theorem eigenEuler_geometric_tendsto_completion20261011
    (scales : ℕ → ℝ) (diverges : Tendsto scales atTop atTop)
    (steps : ℕ → ℕ) (time : ℝ)
    (timeLimit : Tendsto (fun depth => (steps depth : ℝ) / scales depth) atTop (𝓝 time))
    (eigenvalue : ℝ) (eigenvalueNonnegative : 0 ≤ eigenvalue) :
    Tendsto (fun depth => (1 - eigenvalue / scales depth) ^ steps depth) atTop
      (𝓝 (Real.exp (-eigenvalue * time))) := by
  by_cases zero : eigenvalue = 0
  · simp only [zero, zero_div, sub_zero, one_pow, neg_zero, zero_mul, Real.exp_zero]
    exact tendsto_const_nhds
  have positive : 0 < eigenvalue := lt_of_le_of_ne eigenvalueNonnegative (Ne.symm zero)
  have exponents := timeLimit.mul (eigenEuler_log_scale_completion20261011 scales diverges eigenvalue positive)
  have exponentLimit : Tendsto (fun depth => (steps depth : ℝ) * Real.log (1 - eigenvalue / scales depth))
      atTop (𝓝 (-eigenvalue * time)) := by
    apply Tendsto.congr' _ (by simpa only [mul_comm time] using exponents)
    filter_upwards [diverges.eventually (eventually_gt_atTop 0)] with depth scalePositive
    field_simp
  have limit := Real.continuous_exp.continuousAt.tendsto.comp exponentLimit
  apply Tendsto.congr' _ limit
  filter_upwards [diverges.eventually (eventually_gt_atTop eigenvalue)] with depth scaleBound
  have scalePositive : 0 < scales depth := positive.trans scaleBound
  have basePositive : 0 < 1 - eigenvalue / scales depth := sub_pos.mpr ((div_lt_one scalePositive).mpr scaleBound)
  change Real.exp ((steps depth : ℝ) * Real.log (1 - eigenvalue / scales depth)) = _
  rw [Real.exp_nat_mul, Real.exp_log basePositive]

end
end IGSIII34.Diffusion
