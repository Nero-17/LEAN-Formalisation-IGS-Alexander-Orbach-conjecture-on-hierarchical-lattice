import IGSIII4.SpectralDensity.ActualDensityCompletion
import IGSIII4.SpectralDensity.LogarithmicRemainder

/-! The natural resistance factor of the actual Appendix C family has a
bounded error after subtracting the principal logarithmic term. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Filter Topology Asymptotics

theorem appendix_actual_natural_log_remainder_bounds
    (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      Real.log (1 / (40 * ((⌈base⌉₊ : ℝ) + 2))) ≤
        Real.log (appendixNaturalCompletion base length).growth - (length : ℝ) * Real.log base ∧
      Real.log (appendixNaturalCompletion base length).growth - (length : ℝ) * Real.log base ≤
        Real.log (2 * (2 + 8 / Real.log base)) := by
  have lowerPositive : 0 < 1 / (40 * ((⌈base⌉₊ : ℝ) + 2)) := by positivity
  have upperPositive : 0 < 2 + 8 / Real.log base := by
    have := Real.log_pos baseAboveOne
    positivity
  have exponentialBounds : ∀ᶠ length : ℕ in atTop,
      (1 / (40 * ((⌈base⌉₊ : ℝ) + 2))) * (length : ℝ) ^ 0 * base ^ length ≤
          (appendixNaturalCompletion base length).growth ∧
      (appendixNaturalCompletion base length).growth ≤
        (2 * (2 + 8 / Real.log base)) * (length : ℝ) ^ 0 * base ^ length := by
    filter_upwards [appendix_actual_natural_growth_bounds base baseAboveOne] with length bounds
    obtain ⟨blockLower, blockUpper⟩ := blockCount_bounds base baseAboveOne.le length
    simp only [pow_zero, mul_one]
    constructor
    · exact (mul_le_mul_of_nonneg_left blockLower lowerPositive.le).trans bounds.1
    · have := bounds.2.trans (mul_le_mul_of_nonneg_left blockUpper upperPositive.le)
      nlinarith
  simpa only [Nat.cast_zero, zero_mul, add_zero] using
    logarithmic_remainder_bounds_of_polynomial_exponential_bounds
      (fun length => (appendixNaturalCompletion base length).growth)
      (1 / (40 * ((⌈base⌉₊ : ℝ) + 2))) (2 * (2 + 8 / Real.log base)) base 0
      lowerPositive (by positivity) (by linarith) exponentialBounds

/-- The actual natural resistance completion satisfies
`log λ = length * log base + O_base(1)`. -/
theorem appendix_actual_natural_log_asymptotic
    (base : ℝ) (baseAboveOne : 1 < base) :
    (fun length : ℕ => Real.log (appendixNaturalCompletion base length).growth -
      (length : ℝ) * Real.log base) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  isBigO_one_of_eventually_bounded _
    (Real.log (1 / (40 * ((⌈base⌉₊ : ℝ) + 2))))
    (Real.log (2 * (2 + 8 / Real.log base)))
    (appendix_actual_natural_log_remainder_bounds base baseAboveOne)

end
end IGSIII4.SpectralDensity.ActualFamily
