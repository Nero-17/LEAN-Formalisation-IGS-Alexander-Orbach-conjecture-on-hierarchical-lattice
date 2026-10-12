import IGSIII4.SpectralDensity.Asymptotics20261012

/-! Explicit logarithmic consequences of two-sided polynomial/exponential
bounds. These are analytic lemmas; graph-specific estimates are separate. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology

theorem normalized_polynomial_exponential_log_limit
    (coefficient base : ℝ) (order : ℕ)
    (coefficientPositive : 0 < coefficient) (basePositive : 0 < base) :
    Tendsto (fun depth : ℕ =>
      Real.log (coefficient * (depth : ℝ) ^ order * base ^ depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base)) := by
  have constantLimit : Tendsto (fun depth : ℕ => Real.log coefficient / (depth : ℝ))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have logarithmLimit : Tendsto (fun depth : ℕ => Real.log (depth : ℝ) / (depth : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have sumLimit := (constantLimit.add (logarithmLimit.const_mul (order : ℝ))).add_const (Real.log base)
  simp only [mul_zero, zero_add] at sumLimit
  apply sumLimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with depth depthPositive
  have depthRealPositive : 0 < (depth : ℝ) := by exact_mod_cast (by omega : 0 < depth)
  rw [Real.log_mul (mul_ne_zero (ne_of_gt coefficientPositive)
    (pow_ne_zero _ (ne_of_gt depthRealPositive))) (pow_ne_zero _ (ne_of_gt basePositive))]
  rw [Real.log_mul (ne_of_gt coefficientPositive) (pow_ne_zero _ (ne_of_gt depthRealPositive))]
  simp only [Real.log_pow]
  field_simp
  <;> ring

theorem normalized_log_limit_of_polynomial_exponential_bounds
    (growth : ℕ → ℝ) (lowerCoefficient upperCoefficient base : ℝ) (order : ℕ)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (basePositive : 0 < base)
    (bounds : ∀ᶠ depth : ℕ in atTop,
      lowerCoefficient * (depth : ℝ) ^ order * base ^ depth ≤ growth depth ∧
      growth depth ≤ upperCoefficient * (depth : ℝ) ^ order * base ^ depth) :
    Tendsto (fun depth => Real.log (growth depth) / (depth : ℝ))
      atTop (𝓝 (Real.log base)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (normalized_polynomial_exponential_log_limit lowerCoefficient base order lowerPositive basePositive)
    (normalized_polynomial_exponential_log_limit upperCoefficient base order upperPositive basePositive) ?_ ?_
  · filter_upwards [bounds, eventually_ge_atTop (1 : ℕ)] with depth depthBounds depthPositive
    have depthRealPositive : 0 < (depth : ℝ) := by exact_mod_cast (by omega : 0 < depth)
    have lowerTermPositive : 0 < lowerCoefficient * (depth : ℝ) ^ order * base ^ depth := by positivity
    exact div_le_div_of_nonneg_right (Real.log_le_log lowerTermPositive depthBounds.1)
      (le_of_lt depthRealPositive)
  · filter_upwards [bounds, eventually_ge_atTop (1 : ℕ)] with depth depthBounds depthPositive
    have depthRealPositive : 0 < (depth : ℝ) := by exact_mod_cast (by omega : 0 < depth)
    have lowerTermPositive : 0 < lowerCoefficient * (depth : ℝ) ^ order * base ^ depth := by positivity
    have growthPositive : 0 < growth depth := lowerTermPositive.trans_le depthBounds.1
    exact div_le_div_of_nonneg_right (Real.log_le_log growthPositive depthBounds.2)
      (le_of_lt depthRealPositive)

end
end IGSIII4.SpectralDensity
