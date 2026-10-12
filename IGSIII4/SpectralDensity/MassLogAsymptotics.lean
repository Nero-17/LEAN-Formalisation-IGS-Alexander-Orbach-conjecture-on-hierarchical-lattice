import IGSIII4.SpectralDensity.ActualSharpMassBounds
import IGSIII4.SpectralDensity.LogarithmicRemainder

/-! The full Perron mass includes all retained child states, and its
logarithmic asymptotic retains the additional `log length` term. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Filter Topology Asymptotics

theorem appendix_actual_mass_log_remainder_bounds
    (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      Real.log (1 / 3 : ℝ) ≤
        Real.log (actualMassGrowth (appendixRule base length)
          (appendixCriticalProbability base length)) -
          ((length : ℝ) * (Real.log base + Real.log (4 / 3 : ℝ)) + Real.log (length : ℝ)) ∧
      Real.log (actualMassGrowth (appendixRule base length)
          (appendixCriticalProbability base length)) -
          ((length : ℝ) * (Real.log base + Real.log (4 / 3 : ℝ)) + Real.log (length : ℝ)) ≤
        Real.log (204 : ℝ) := by
  have exponentialBounds : ∀ᶠ length : ℕ in atTop,
      (1 / 3 : ℝ) * (length : ℝ) ^ 1 * (base * (4 / 3 : ℝ)) ^ length ≤
          actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length) ∧
      actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length) ≤
        204 * (length : ℝ) ^ 1 * (base * (4 / 3 : ℝ)) ^ length := by
    filter_upwards [appendix_actual_mass_sharp_bounds base baseAboveOne,
      eventually_ge_atTop (1 : ℕ)] with length bounds lengthPositive
    obtain ⟨productLower, productUpper⟩ := count_product_bounds base baseAboveOne.le length lengthPositive
    have scaleAboveOne : 1 ≤ (length : ℝ) * (base * (4 / 3 : ℝ)) ^ length := by
      apply one_le_mul_of_one_le_of_one_le (by exact_mod_cast lengthPositive)
      apply one_le_pow₀
      nlinarith
    simp only [pow_one]
    constructor <;> nlinarith [bounds.1, bounds.2]
  simpa only [Nat.cast_one, one_mul,
    Real.log_mul (by linarith : base ≠ 0) (by norm_num : (4 / 3 : ℝ) ≠ 0)] using
    logarithmic_remainder_bounds_of_polynomial_exponential_bounds
      (fun length => actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length))
      (1 / 3 : ℝ) 204 (base * (4 / 3 : ℝ)) 1
      (by norm_num) (by norm_num) (by positivity) exponentialBounds

/-- The full Perron mass of the actual family satisfies
`log ρ = length * (log base + log (4/3)) + log length + O(1)`. -/
theorem appendix_actual_mass_log_asymptotic
    (base : ℝ) (baseAboveOne : 1 < base) :
    (fun length : ℕ =>
      Real.log (actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length)) -
        ((length : ℝ) * (Real.log base + Real.log (4 / 3 : ℝ)) + Real.log (length : ℝ)))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  isBigO_one_of_eventually_bounded _ (Real.log (1 / 3 : ℝ)) (Real.log (204 : ℝ))
    (appendix_actual_mass_log_remainder_bounds base baseAboveOne)

theorem appendix_patched_actual_mass_log_asymptotic
    (base : ℝ) (baseAboveOne : 1 < base) :
    (fun length : ℕ =>
      Real.log (actualMassGrowth (appendixRule base (max length 2))
        (appendixCriticalProbability base (max length 2))) -
        ((length : ℝ) * (Real.log base + Real.log (4 / 3 : ℝ)) + Real.log (length : ℝ)))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  apply isBigO_one_of_eventually_bounded _ (Real.log (1 / 3 : ℝ)) (Real.log (204 : ℝ))
  filter_upwards [appendix_actual_mass_log_remainder_bounds base baseAboveOne,
    eventually_ge_atTop (2 : ℕ)] with length bounds lengthLarge
  simpa only [max_eq_left lengthLarge] using bounds

end
end IGSIII4.SpectralDensity.ActualFamily
