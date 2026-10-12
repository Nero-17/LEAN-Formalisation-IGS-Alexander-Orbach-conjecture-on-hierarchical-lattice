import IGSIII4.SpectralDensity.CeilingGrowth20261012

/-! The density conclusion only needs exponential mass growth. The classical
edge-count bound gives a sufficient polynomial factor in the upper estimate. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology

theorem normalized_log_limit_of_mixed_polynomial_bounds
    (growth : ℕ → ℝ) (lowerCoefficient upperCoefficient base : ℝ)
    (lowerOrder upperOrder : ℕ)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (basePositive : 0 < base)
    (bounds : ∀ᶠ depth : ℕ in atTop,
      lowerCoefficient * (depth : ℝ) ^ lowerOrder * base ^ depth ≤ growth depth ∧
      growth depth ≤ upperCoefficient * (depth : ℝ) ^ upperOrder * base ^ depth) :
    Tendsto (fun depth => Real.log (growth depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (normalized_polynomial_exponential_log_limit lowerCoefficient base lowerOrder lowerPositive basePositive)
    (normalized_polynomial_exponential_log_limit upperCoefficient base upperOrder upperPositive basePositive) ?_ ?_
  · filter_upwards [bounds, eventually_ge_atTop (1 : ℕ)] with depth depthBounds depthPositive
    have depthRealPositive : 0 < (depth : ℝ) := by exact_mod_cast (by omega : 0 < depth)
    have lowerTermPositive : 0 < lowerCoefficient * (depth : ℝ) ^ lowerOrder * base ^ depth := by positivity
    exact div_le_div_of_nonneg_right (Real.log_le_log lowerTermPositive depthBounds.1)
      depthRealPositive.le
  · filter_upwards [bounds, eventually_ge_atTop (1 : ℕ)] with depth depthBounds depthPositive
    have depthRealPositive : 0 < (depth : ℝ) := by exact_mod_cast (by omega : 0 < depth)
    have lowerTermPositive : 0 < lowerCoefficient * (depth : ℝ) ^ lowerOrder * base ^ depth := by positivity
    have growthPositive : 0 < growth depth := lowerTermPositive.trans_le depthBounds.1
    exact div_le_div_of_nonneg_right (Real.log_le_log growthPositive depthBounds.2)
      depthRealPositive.le

theorem mass_normalized_log_limit_of_edge_count_bound
    (base : ℝ) (baseAboveOne : 1 < base) (massGrowth : ℕ → ℝ)
    (bounds : ∀ᶠ depth : ℕ in atTop,
      (1 / 3 : ℝ) * (blockCount base depth : ℝ) * (pathCount depth : ℝ) ≤ massGrowth depth ∧
      massGrowth depth ≤ 4 + (blockCount base depth : ℝ) * (pathCount depth : ℝ) * (depth : ℝ)) :
    Tendsto (fun depth => Real.log (massGrowth depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base + Real.log (4 / 3 : ℝ))) := by
  have eventualBounds : ∀ᶠ depth : ℕ in atTop,
      (1 / 3 : ℝ) * (depth : ℝ) ^ 1 * (base * (4 / 3 : ℝ)) ^ depth ≤ massGrowth depth ∧
      massGrowth depth ≤ 8 * (depth : ℝ) ^ 2 * (base * (4 / 3 : ℝ)) ^ depth := by
    filter_upwards [bounds, eventually_ge_atTop (1 : ℕ)] with depth depthBounds depthPositive
    obtain ⟨productLower, productUpper⟩ := count_product_bounds base baseAboveOne.le depth depthPositive
    have depthAboveOne : 1 ≤ (depth : ℝ) := by exact_mod_cast depthPositive
    have powerAboveOne : 1 ≤ (base * (4 / 3 : ℝ)) ^ depth := by
      apply one_le_pow₀
      nlinarith
    have scaleAboveOne : 1 ≤ (depth : ℝ) ^ 2 * (base * (4 / 3 : ℝ)) ^ depth :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ depthAboveOne) powerAboveOne
    constructor
    · simpa only [pow_one, mul_assoc] using (mul_le_mul_of_nonneg_left productLower (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans
        (by simpa only [mul_assoc] using depthBounds.1)
    · have upper := mul_le_mul_of_nonneg_right productUpper (by positivity : 0 ≤ (depth : ℝ))
      nlinarith [depthBounds.2]
  have limit := normalized_log_limit_of_mixed_polynomial_bounds massGrowth (1 / 3) 8
    (base * (4 / 3)) 1 2 (by norm_num) (by norm_num) (by positivity) eventualBounds
  rwa [Real.log_mul (by linarith : base ≠ 0) (by norm_num : (4 / 3 : ℝ) ≠ 0)] at limit

end
end IGSIII4.SpectralDensity
