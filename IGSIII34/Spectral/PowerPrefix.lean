import IGSIII34.Spectral.LaplaceMonotone
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integrating a subcritical power upper bound in the Tauberian argument. -/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Set

theorem integral_power_prefix (exponent time : ℝ) (exponentBound : -1 < exponent)
    (timePositive : 0 < time) :
    (∫ other in Ioc 0 time, other ^ exponent) = time ^ (exponent + 1) / (exponent + 1) := by
  have formula := integral_rpow
    (a := (0 : ℝ)) (b := time) (Or.inl exponentBound)
  rw [intervalIntegral.integral_of_le timePositive.le,
    Real.zero_rpow (by linarith : exponent + 1 ≠ 0), sub_zero] at formula
  exact formula

theorem integrable_kernel_prefix_of_power_bound
    (kernel : ℝ → ℝ) (coefficient exponent time : ℝ)
    (measurable : Measurable kernel) (coefficientNonnegative : 0 ≤ coefficient)
    (exponentBound : exponent < 1)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (upper : ∀ other ∈ Ioc 0 time, kernel other ≤ coefficient * other ^ (-exponent)) :
    IntegrableOn kernel (Ioc 0 time) := by
  have powerIntegrable : IntegrableOn (fun other : ℝ => other ^ (-exponent)) (Ioc 0 time) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := time) (by linarith : -1 < -exponent)).1
  apply (powerIntegrable.const_mul coefficient).mono' measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with other member
  simpa only [Real.norm_eq_abs, abs_of_nonneg (nonnegative other member.1)] using
    upper other member

theorem integral_kernel_prefix_le_power
    (kernel : ℝ → ℝ) (coefficient exponent time : ℝ)
    (measurable : Measurable kernel) (coefficientNonnegative : 0 ≤ coefficient)
    (exponentBound : exponent < 1) (timePositive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (upper : ∀ other ∈ Ioc 0 time, kernel other ≤ coefficient * other ^ (-exponent)) :
    (∫ other in Ioc 0 time, kernel other) ≤
      coefficient * time ^ (1 - exponent) / (1 - exponent) := by
  have powerIntegrable : IntegrableOn (fun other : ℝ => other ^ (-exponent)) (Ioc 0 time) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := time) (by linarith : -1 < -exponent)).1
  have bound := integral_mono_ae
    (integrable_kernel_prefix_of_power_bound kernel coefficient exponent time
      measurable coefficientNonnegative exponentBound nonnegative upper)
    (powerIntegrable.const_mul coefficient)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with other member
      exact upper other member)
  calc
    _ ≤ _ := bound
    _ = _ := by
      rw [integral_const_mul, integral_power_prefix (-exponent) time (by linarith) timePositive]
      simp only [show -exponent + 1 = 1 - exponent by ring]
      ring

theorem diagonalLaplace_split_power_le
    (kernel : ℝ → ℝ) (coefficient exponent parameter time : ℝ)
    (measurable : Measurable kernel) (coefficientNonnegative : 0 ≤ coefficient)
    (exponentBound : exponent < 1) (parameterPositive : 0 < parameter) (timePositive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : IntegrableOn (fun other => Real.exp (-parameter * other) * kernel other) (Ioi 0))
    (upper : ∀ other ∈ Ioc 0 time, kernel other ≤ coefficient * other ^ (-exponent)) :
    diagonalLaplace kernel parameter ≤
      coefficient * time ^ (1 - exponent) / (1 - exponent) + kernel time / parameter := by
  exact (diagonalLaplace_split_le kernel parameter time parameterPositive timePositive nonnegative
    decreasing integrable (integrable_kernel_prefix_of_power_bound kernel coefficient exponent time
      measurable coefficientNonnegative exponentBound nonnegative upper)).trans
      (add_le_add (integral_kernel_prefix_le_power kernel coefficient exponent time measurable
        coefficientNonnegative exponentBound timePositive nonnegative upper) le_rfl)

end
end IGSIII34.Spectral

