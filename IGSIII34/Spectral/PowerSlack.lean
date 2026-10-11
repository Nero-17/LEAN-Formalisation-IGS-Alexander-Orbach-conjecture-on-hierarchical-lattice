import IGSIII34.Spectral.LogCorrectedDimension

/-! Spectral dimension from arbitrary slack in the small-time power bounds. -/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open Filter
open scoped Topology

theorem spectral_ratio_lower_of_power_bound
    (value time coefficient exponent : ℝ)
    (timePositive : 0 < time) (timeSmall : time < 1) (coefficientPositive : 0 < coefficient)
    (lower : coefficient * time ^ (-exponent) ≤ value) :
    2 * exponent + -2 * Real.log coefficient / Real.log time ≤
      -2 * Real.log value / Real.log time := by
  have logarithmNegative := Real.log_neg timePositive timeSmall
  have logarithmic := Real.log_le_log
    (mul_pos coefficientPositive (Real.rpow_pos_of_pos timePositive _)) lower
  rw [Real.log_mul coefficientPositive.ne' (Real.rpow_pos_of_pos timePositive _).ne',
    Real.log_rpow timePositive] at logarithmic
  have multiplied := mul_le_mul_of_nonneg_left logarithmic
    (div_pos_of_neg_of_neg (by norm_num : (-2 : ℝ) < 0) logarithmNegative).le
  calc
    _ = (-2 / Real.log time) * (Real.log coefficient + -exponent * Real.log time) := by
      field_simp [logarithmNegative.ne] <;> ring
    _ ≤ _ := multiplied
    _ = _ := by ring

theorem spectral_ratio_upper_of_power_bound
    (value time coefficient exponent : ℝ)
    (valuePositive : 0 < value) (timePositive : 0 < time) (timeSmall : time < 1)
    (coefficientPositive : 0 < coefficient)
    (upper : value ≤ coefficient * time ^ (-exponent)) :
    -2 * Real.log value / Real.log time ≤
      2 * exponent + -2 * Real.log coefficient / Real.log time := by
  have logarithmNegative := Real.log_neg timePositive timeSmall
  have logarithmic := Real.log_le_log valuePositive upper
  rw [Real.log_mul coefficientPositive.ne' (Real.rpow_pos_of_pos timePositive _).ne',
    Real.log_rpow timePositive] at logarithmic
  have multiplied := mul_le_mul_of_nonneg_left logarithmic
    (div_pos_of_neg_of_neg (by norm_num : (-2 : ℝ) < 0) logarithmNegative).le
  calc
    _ = (-2 / Real.log time) * Real.log value := by ring
    _ ≤ _ := multiplied
    _ = _ := by field_simp [logarithmNegative.ne] <;> ring

theorem tendsto_power_logarithmic_comparison (coefficient exponent : ℝ) :
    Tendsto (fun time : ℝ => 2 * exponent + -2 * Real.log coefficient / Real.log time)
      (𝓝[>] 0) (𝓝 (2 * exponent)) := by
  have limit := (tendsto_inv_log_nhdsGT_zero.const_mul (-2 * Real.log coefficient)).const_add (2 * exponent)
  simpa [div_eq_mul_inv] using limit

theorem spectral_dimension_of_arbitrary_power_slack
    (kernel : ℝ → ℝ) (exponent : ℝ)
    (lower : ∀ smaller : ℝ, smaller < exponent → ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ᶠ time : ℝ in 𝓝[>] 0, coefficient * time ^ (-smaller) ≤ kernel time)
    (upper : ∀ larger : ℝ, exponent < larger → ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ᶠ time : ℝ in 𝓝[>] 0, kernel time ≤ coefficient * time ^ (-larger)) :
    Tendsto (fun time => -2 * Real.log (kernel time) / Real.log time)
      (𝓝[>] 0) (𝓝 (2 * exponent)) := by
  have timeSmall : ∀ᶠ time : ℝ in 𝓝[>] 0, time < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  obtain ⟨positiveCoefficient, coefficientPositive, positiveLower⟩ := lower (exponent - 1) (by linarith)
  have kernelPositive : ∀ᶠ time : ℝ in 𝓝[>] 0, 0 < kernel time := by
    filter_upwards [self_mem_nhdsWithin, positiveLower] with time positive bound
    exact (mul_pos coefficientPositive (Real.rpow_pos_of_pos positive _)).trans_le bound
  apply tendsto_order.mpr
  constructor
  · intro cut strict
    let smaller := (cut / 2 + exponent) / 2
    have smallerBound : smaller < exponent := by dsimp [smaller]; linarith
    have cutBound : cut < 2 * smaller := by dsimp [smaller]; linarith
    obtain ⟨coefficient, coefficientPositive, powerBound⟩ := lower smaller smallerBound
    have comparisonAbove := (tendsto_order.mp (tendsto_power_logarithmic_comparison coefficient smaller)).1 cut cutBound
    filter_upwards [self_mem_nhdsWithin, timeSmall, powerBound, comparisonAbove] with time positive small bound above
    exact above.trans_le (spectral_ratio_lower_of_power_bound (kernel time) time coefficient smaller
      positive small coefficientPositive bound)
  · intro cut strict
    let larger := (cut / 2 + exponent) / 2
    have largerBound : exponent < larger := by dsimp [larger]; linarith
    have cutBound : 2 * larger < cut := by dsimp [larger]; linarith
    obtain ⟨coefficient, coefficientPositive, powerBound⟩ := upper larger largerBound
    have comparisonBelow := (tendsto_order.mp (tendsto_power_logarithmic_comparison coefficient larger)).2 cut cutBound
    filter_upwards [self_mem_nhdsWithin, timeSmall, kernelPositive, powerBound, comparisonBelow]
      with time positive small positiveKernel bound below
    exact (spectral_ratio_upper_of_power_bound (kernel time) time coefficient larger
      positiveKernel positive small coefficientPositive bound).trans_lt below

end
end IGSIII34.Spectral
