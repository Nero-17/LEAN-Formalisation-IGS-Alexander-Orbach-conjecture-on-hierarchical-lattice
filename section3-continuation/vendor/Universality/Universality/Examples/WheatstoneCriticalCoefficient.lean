import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Universality.Examples.WheatstonePowerResponse
import Universality.Analysis.LocalExponentialComparison

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Set Filter Polynomial
open scoped Topology

def wheatstoneCriticalNormalizedCoefficient (p : ℝ) : ℝ :=
  (wheatstoneRealCrossing.derivative.eval p ^ 3 / 5) *
    wheatstoneRealSecant.eval p ^ (Real.log 5 / Real.log (13 / 8) - 3)

theorem wheatstone_critical_normalized_coefficient_half :
    wheatstoneCriticalNormalizedCoefficient (1 / 2) = 1 := by
  have hlog : Real.log (13 / 8 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hvalue : Real.log (13 / 8 : ℝ) * (Real.log 5 / Real.log (13 / 8) - 3) =
      Real.log 5 - 3 * Real.log (13 / 8) := by field_simp
  have hpower : (13 / 8 : ℝ) ^ (Real.log 5 / Real.log (13 / 8) - 3) = 5 / (13 / 8 : ℝ) ^ 3 := by
    rw [Real.rpow_def_of_pos (by norm_num), hvalue, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    have hh : 3 * Real.log (13 / 8 : ℝ) = Real.log ((13 / 8 : ℝ) ^ (3 : ℕ)) := by
      rw [Real.log_pow]; norm_num
    rw [hh, Real.exp_log (by norm_num)]
  unfold wheatstoneCriticalNormalizedCoefficient
  rw [wheatstone_real_secant_half, (wheatstone_real_polynomial_derivatives (1/2)).1]
  norm_num only at *
  norm_num [hpower]

theorem wheatstone_real_secant_le_half (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    wheatstoneRealSecant.eval p ≤ 13 / 8 := by
  have hsquare : (p - 1/2)^2 ≤ (1/4 : ℝ) := by nlinarith [hp.1, hp.2]
  have hnonnegative : 0 ≤ (p - 1/2)^2 := sq_nonneg _
  have hproduct := mul_nonneg hnonnegative (show 0 ≤ 3 - 2*(p - 1/2)^2 by linarith)
  have hidentity : wheatstoneRealSecant.eval p = 13/8 - 3*(p - 1/2)^2 + 2*(p - 1/2)^4 := by
    simp [wheatstoneRealSecant]
    <;> ring
  rw [hidentity]
  nlinarith

theorem wheatstone_critical_normalized_coefficient_le_one (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    wheatstoneCriticalNormalizedCoefficient p ≤ 1 := by
  have hs := (wheatstone_response_polynomial_signs p hp).1
  have hderivative := pow_le_pow_left₀ hs.1 hs.2 3
  have hsecant := Real.rpow_le_rpow (wheatstone_real_secant_pos p hp).le
    (wheatstone_real_secant_le_half p hp) wheatstone_response_order_bounds.1.le
  have hh := mul_le_mul (div_le_div_of_nonneg_right hderivative (by norm_num : (0 : ℝ) ≤ 5))
    hsecant (Real.rpow_nonneg (wheatstone_real_secant_pos p hp).le _)
    (by norm_num : (0 : ℝ) ≤ (13/8)^3/5)
  have hcenter := wheatstone_critical_normalized_coefficient_half
  unfold wheatstoneCriticalNormalizedCoefficient at hcenter ⊢
  rw [wheatstone_real_secant_half, (wheatstone_real_polynomial_derivatives (1/2)).1] at hcenter
  norm_num only at hcenter
  exact hh.trans_eq (by convert hcenter using 1 <;> norm_num)

theorem wheatstone_critical_normalized_coefficient_exp_bound :
    ∃ rate : ℝ, 0 < rate ∧ ∀ᶠ p : ℝ in 𝓝 (1/2),
      1 ≤ Real.exp (rate * |p - 1/2|) * wheatstoneCriticalNormalizedCoefficient p := by
  have hsecant : DifferentiableAt ℝ (fun p : ℝ =>
      wheatstoneRealSecant.eval p ^ (Real.log 5 / Real.log (13/8) - 3)) (1/2) := by
    apply (wheatstoneRealSecant.hasDerivAt (1/2)).differentiableAt.rpow_const
    rw [wheatstone_real_secant_half]
    norm_num
  have hdiff : DifferentiableAt ℝ wheatstoneCriticalNormalizedCoefficient (1/2) :=
    (((wheatstoneRealCrossing.derivative.hasDerivAt (1/2)).differentiableAt.pow 3).div_const 5).mul hsecant
  obtain ⟨rate, hrate, hb⟩ := positive_differentiable_local_exponential_comparison
    wheatstoneCriticalNormalizedCoefficient (1/2) hdiff (by rw [wheatstone_critical_normalized_coefficient_half]; norm_num)
  refine ⟨rate, hrate, ?_⟩
  filter_upwards [hb] with p hp
  simpa only [wheatstone_critical_normalized_coefficient_half] using hp.2.2

end
end Universality
