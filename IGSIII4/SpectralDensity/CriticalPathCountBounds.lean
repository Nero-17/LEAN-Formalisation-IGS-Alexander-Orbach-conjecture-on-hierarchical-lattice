import IGSIII4.SpectralDensity.ActualBinomialConditional

/-! The complete chain of path-count inequalities in Appendix C, including
the intermediate logarithm of the ceiling block count. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Filter Topology

theorem blockCount_log_upper (base : ℝ) (baseAboveOne : 1 < base)
    (length : ℕ) (lengthLarge : 4 ≤ length) :
    Real.log (8 * (blockCount base length : ℝ)) <
      ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ) := by
  have blocksPositive : 0 < (blockCount base length : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity : 0 < base ^ length) :
      0 < blockCount base length)
  have blockLogUpper := Real.log_le_log (by positivity : 0 < 8 * (blockCount base length : ℝ))
    (mul_le_mul_of_nonneg_left (blockCount_bounds base baseAboveOne.le length).2 (by norm_num : (0 : ℝ) ≤ 8))
  have logarithmIdentity : Real.log (8 * (2 * base ^ length)) =
      4 * Real.log 2 + (length : ℝ) * Real.log base := by
    rw [show 8 * (2 * base ^ length) = (2 : ℝ) ^ 4 * base ^ length by ring,
      Real.log_mul (by norm_num) (by positivity : base ^ length ≠ 0), Real.log_pow, Real.log_pow]
    norm_num
  rw [logarithmIdentity] at blockLogUpper
  have logTwoUpper : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have logBaseUpper : Real.log base ≤ (⌈base⌉₊ : ℝ) - 1 :=
    (Real.log_le_sub_one_of_pos (by linarith : 0 < base)).trans (by linarith [Nat.le_ceil base])
  have lengthRealLarge : 4 ≤ (length : ℝ) := by exact_mod_cast lengthLarge
  nlinarith [mul_le_mul_of_nonneg_left logBaseUpper (Nat.cast_nonneg length)]

theorem appendix_success_mean_refined_bounds_eventually
    (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      (length : ℝ) * Real.log base / 2 <
        (pathCount length : ℝ) * appendixCriticalProbability base length ^ length ∧
      (pathCount length : ℝ) * appendixCriticalProbability base length ^ length <
        Real.log (8 * (blockCount base length : ℝ)) ∧
      Real.log (8 * (blockCount base length : ℝ)) <
        ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ) ∧
      IGSIII34.Probability.finiteMean
        (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
        (fun configuration => (successCount (pathCount length) configuration : ℝ)) <
          2 * ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ) := by
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    appendix_success_mean_bounds_eventually base baseAboveOne,
    appendix_conditional_count_and_inverse_bounds_eventually base baseAboveOne,
    eventually_ge_atTop (4 : ℕ)] with length interval meanBounds conditionalBounds lengthLarge
  have lengthAtLeastTwo : 2 ≤ length := by omega
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthAtLeastTwo
  have powerHalf : appendixCriticalProbability base length ^ length ≤ 1 / 2 := by
    calc
      _ ≤ (4 / 5 : ℝ) ^ length := pow_le_pow_left₀ positive.le interval.2.le _
      _ ≤ (4 / 5 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) lengthLarge
      _ ≤ _ := by norm_num
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have logarithmBounds := critical_success_mean_log_bounds (blockCount base length) (pathCount length)
    (length - 2) blocksPositive _ interval.1 interval.2
    (by simpa only [Nat.sub_add_cancel lengthAtLeastTwo] using powerHalf) fixedPoint
  simp only [Nat.sub_add_cancel lengthAtLeastTwo] at logarithmBounds
  exact ⟨meanBounds.1, logarithmBounds.2, blockCount_log_upper base baseAboveOne length lengthLarge,
    conditionalBounds.1⟩

end
end IGSIII4.SpectralDensity.ActualFamily
