import IGSIII34.AO.Dimension

set_option autoImplicit false
namespace IGSIII34
noncomputable section

theorem subdivided_diamond_logarithmic_bound_identity :
    2 * Real.log 20 / (Real.log 20 + Real.log 5) = Real.log 20 / Real.log 10 := by
  have denominator : Real.log 20 + Real.log 5 = 2 * Real.log 10 := by
    rw [← Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    convert Real.log_pow (10 : ℝ) 2 using 1 <;> norm_num
  rw [denominator]
  ring

theorem subdivided_diamond_logarithmic_bound_lt_four_thirds :
    Real.log 20 / Real.log 10 < (4 / 3 : ℝ) := by
  have comparison := Real.log_lt_log (by norm_num : 0 < (20 : ℝ) ^ 3)
    (by norm_num : (20 : ℝ) ^ 3 < (10 : ℝ) ^ 4)
  rw [Real.log_pow, Real.log_pow] at comparison
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 10))).mpr
  norm_num at comparison ⊢
  linarith

/-- The worked example's bound uses only the actual mass and resistance
growth inequalities, without computing its random electrical eigenlaw. -/
theorem spectral_bound_of_twenty_edges_five_resistance
    {massGrowth resistanceGrowth : ℝ}
    (massSuperunit : 1 < massGrowth) (massUpper : massGrowth ≤ 20)
    (resistanceLower : 5 ≤ resistanceGrowth) :
    typicalSpectralDimension massGrowth resistanceGrowth ≤ Real.log 20 / Real.log 10 ∧
      typicalSpectralDimension massGrowth resistanceGrowth < (4 / 3 : ℝ) := by
  have massPositive : 0 < massGrowth := lt_trans zero_lt_one massSuperunit
  have resistancePositive : 0 < resistanceGrowth := lt_of_lt_of_le (by norm_num) resistanceLower
  have massLogPositive := Real.log_pos massSuperunit
  have resistanceLogPositive := Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 5) resistanceLower)
  have massLogUpper := Real.log_le_log massPositive massUpper
  have resistanceLogLower := Real.log_le_log (by norm_num : (0 : ℝ) < 5) resistanceLower
  have twentyLogPositive := Real.log_pos (by norm_num : (1 : ℝ) < 20)
  have fiveLogPositive := Real.log_pos (by norm_num : (1 : ℝ) < 5)
  have upper : typicalSpectralDimension massGrowth resistanceGrowth ≤
      2 * Real.log 20 / (Real.log 20 + Real.log 5) := by
    unfold typicalSpectralDimension
    rw [Real.log_mul massPositive.ne' resistancePositive.ne']
    apply (div_le_div_iff₀ (add_pos massLogPositive resistanceLogPositive)
      (add_pos twentyLogPositive fiveLogPositive)).mpr
    nlinarith [mul_le_mul_of_nonneg_right massLogUpper fiveLogPositive.le,
      mul_le_mul_of_nonneg_left resistanceLogLower twentyLogPositive.le]
  rw [subdivided_diamond_logarithmic_bound_identity] at upper
  exact ⟨upper, upper.trans_lt subdivided_diamond_logarithmic_bound_lt_four_thirds⟩

end
end IGSIII34
