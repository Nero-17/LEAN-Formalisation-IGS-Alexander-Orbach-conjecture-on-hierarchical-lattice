import IGSIII4.SpectralDensity.LogGrowth
import Mathlib.Algebra.Order.Floor.Semiring

/-! Exact ceiling-count bounds and their logarithmic consequences for the
family in Appendix C. Resistance and mass estimates are explicit premises;
these lemmas do not assert those estimates for the actual finite networks. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology

def blockCount (base : ℝ) (depth : ℕ) : ℕ := ⌈base ^ depth⌉₊
def pathCount (depth : ℕ) : ℕ := ⌈(depth : ℝ) * (4 / 3 : ℝ) ^ depth⌉₊

theorem ceil_bounds_of_one_le (value : ℝ) (valueAboveOne : 1 ≤ value) :
    value ≤ (⌈value⌉₊ : ℝ) ∧ (⌈value⌉₊ : ℝ) ≤ 2 * value := by
  refine ⟨Nat.le_ceil value, ?_⟩
  have := Nat.ceil_lt_add_one (by linarith : 0 ≤ value)
  linarith

theorem blockCount_bounds (base : ℝ) (baseAboveOne : 1 ≤ base) (depth : ℕ) :
    base ^ depth ≤ (blockCount base depth : ℝ) ∧
    (blockCount base depth : ℝ) ≤ 2 * base ^ depth :=
  ceil_bounds_of_one_le _ (one_le_pow₀ baseAboveOne)

theorem pathCount_bounds (depth : ℕ) (depthPositive : 1 ≤ depth) :
    (depth : ℝ) * (4 / 3 : ℝ) ^ depth ≤ (pathCount depth : ℝ) ∧
    (pathCount depth : ℝ) ≤ 2 * ((depth : ℝ) * (4 / 3 : ℝ) ^ depth) := by
  apply ceil_bounds_of_one_le
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast depthPositive)
    (one_le_pow₀ (by norm_num))

theorem count_product_bounds (base : ℝ) (baseAboveOne : 1 ≤ base)
    (depth : ℕ) (depthPositive : 1 ≤ depth) :
    (depth : ℝ) * (base * (4 / 3 : ℝ)) ^ depth ≤
      (blockCount base depth : ℝ) * (pathCount depth : ℝ) ∧
    (blockCount base depth : ℝ) * (pathCount depth : ℝ) ≤
      4 * ((depth : ℝ) * (base * (4 / 3 : ℝ)) ^ depth) := by
  obtain ⟨blockLower, blockUpper⟩ := blockCount_bounds base baseAboveOne depth
  obtain ⟨pathLower, pathUpper⟩ := pathCount_bounds depth depthPositive
  have basePowerNonnegative : 0 ≤ base ^ depth := pow_nonneg (by linarith) _
  have pathCountNonnegative : 0 ≤ (pathCount depth : ℝ) := Nat.cast_nonneg _
  have pathScaleNonnegative : 0 ≤ (depth : ℝ) * (4 / 3 : ℝ) ^ depth := by positivity
  constructor
  · have productLower := mul_le_mul blockLower pathLower pathScaleNonnegative (Nat.cast_nonneg _)
    calc
      _ = base ^ depth * ((depth : ℝ) * (4 / 3 : ℝ) ^ depth) := by rw [mul_pow]; ring
      _ ≤ _ := productLower
  · have productUpper := mul_le_mul blockUpper pathUpper pathCountNonnegative
      (by positivity : 0 ≤ 2 * base ^ depth)
    calc
      _ ≤ (2 * base ^ depth) * (2 * ((depth : ℝ) * (4 / 3 : ℝ) ^ depth)) := productUpper
      _ = _ := by rw [mul_pow]; ring

theorem resistance_normalized_log_limit_of_block_bounds
    (base : ℝ) (baseAboveOne : 1 < base) (resistanceGrowth : ℕ → ℝ)
    (lowerCoefficient upperCoefficient : ℝ)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (bounds : ∀ᶠ depth : ℕ in atTop,
      lowerCoefficient * (blockCount base depth : ℝ) ≤ resistanceGrowth depth ∧
      resistanceGrowth depth ≤ upperCoefficient * (blockCount base depth : ℝ)) :
    Tendsto (fun depth => Real.log (resistanceGrowth depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base)) := by
  apply normalized_log_limit_of_polynomial_exponential_bounds resistanceGrowth
    lowerCoefficient (2 * upperCoefficient) base 0 lowerPositive (by positivity)
    (by linarith)
  filter_upwards [bounds] with depth depthBounds
  obtain ⟨blockLower, blockUpper⟩ := blockCount_bounds base baseAboveOne.le depth
  simp only [pow_zero, mul_one]
  constructor
  · exact (mul_le_mul_of_nonneg_left blockLower lowerPositive.le).trans depthBounds.1
  · have upperBound := depthBounds.2.trans (mul_le_mul_of_nonneg_left blockUpper upperPositive.le)
    nlinarith

theorem mass_normalized_log_limit_of_count_bounds
    (base : ℝ) (baseAboveOne : 1 < base) (massGrowth : ℕ → ℝ)
    (bounds : ∀ᶠ depth : ℕ in atTop,
      (1 / 3 : ℝ) * (blockCount base depth : ℝ) * (pathCount depth : ℝ) ≤ massGrowth depth ∧
      massGrowth depth ≤ 50 * (blockCount base depth : ℝ) * (pathCount depth : ℝ) + 4) :
    Tendsto (fun depth => Real.log (massGrowth depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base + Real.log (4 / 3 : ℝ))) := by
  have exponentialBasePositive : 0 < base * (4 / 3 : ℝ) := by positivity
  have boundsForLog := normalized_log_limit_of_polynomial_exponential_bounds massGrowth
    (1 / 3 : ℝ) 204 (base * (4 / 3 : ℝ)) 1 (by norm_num) (by norm_num)
    exponentialBasePositive
  have eventualBounds : ∀ᶠ depth : ℕ in atTop,
      (1 / 3 : ℝ) * (depth : ℝ) ^ 1 * (base * (4 / 3 : ℝ)) ^ depth ≤ massGrowth depth ∧
      massGrowth depth ≤ 204 * (depth : ℝ) ^ 1 * (base * (4 / 3 : ℝ)) ^ depth := by
    filter_upwards [bounds, eventually_ge_atTop (1 : ℕ)] with depth depthBounds depthPositive
    obtain ⟨productLower, productUpper⟩ := count_product_bounds base baseAboveOne.le depth depthPositive
    have scaleAboveOne : 1 ≤ (depth : ℝ) * (base * (4 / 3 : ℝ)) ^ depth := by
      apply one_le_mul_of_one_le_of_one_le (by exact_mod_cast depthPositive)
      apply one_le_pow₀
      nlinarith
    simp only [pow_one]
    constructor <;> nlinarith [depthBounds.1, depthBounds.2]
  have limit := boundsForLog eventualBounds
  rwa [Real.log_mul (by linarith : base ≠ 0) (by norm_num : (4 / 3 : ℝ) ≠ 0)] at limit

end
end IGSIII4.SpectralDensity
