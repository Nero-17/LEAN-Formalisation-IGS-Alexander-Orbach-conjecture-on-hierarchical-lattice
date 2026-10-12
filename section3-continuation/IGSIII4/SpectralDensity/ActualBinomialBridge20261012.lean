import IGSIII4.SpectralDensity.ActualBinomialConditional20261012

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork Filter Topology
open IGSIII34.Probability (finiteMean)
open scoped BigOperators

theorem pathStatuses_crossing (paths length : ℕ) (configuration : Fin paths → Configuration length) :
    0 < successCount paths (pathStatuses paths length configuration) ↔ blockCrossing paths length configuration := by
  rw [successCount_positive_iff]
  simp only [pathStatuses, decide_eq_true_eq, blockCrossing]

/-- Conditioning the actual independent path configurations on crossing
pushes forward to the explicit normalized successful-path status law. -/
theorem actual_conditional_path_status_law (paths length : ℕ) (probability : ℝ)
    (response : Configuration paths → ℝ) :
    (∑ configuration : Fin paths → Configuration length,
      if blockCrossing paths length configuration then
        blockWeight paths length probability configuration * response (pathStatuses paths length configuration) else 0) /
          (1 - (1 - probability ^ length) ^ paths) =
      finiteMean (conditionalStatusWeight paths (probability ^ length)) response := by
  rw [conditionalStatusWeight_expectation]
  congr 1
  rw [← path_status_law paths length probability (fun configuration =>
    if 0 < successCount paths configuration then response configuration else 0)]
  apply Finset.sum_congr rfl
  intro configuration _
  simp only [pathStatuses_crossing]
  by_cases crossing : blockCrossing paths length configuration <;> simp [crossing]

theorem appendix_conditional_inverse_upper_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      (length : ℝ) * finiteMean
        (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
        (fun configuration => 1 / (successCount (pathCount length) configuration : ℝ)) < 8 / Real.log base := by
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    appendix_success_mean_bounds_eventually base baseAboveOne, eventually_ge_atTop (4 : ℕ)] with length interval meanBounds lengthLarge
  have lengthAtLeastTwo : 2 ≤ length := by omega
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthAtLeastTwo
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have pathsPositive : 0 < pathCount length := Nat.ceil_pos.mpr (by positivity : 0 < (length : ℝ) * (4 / 3 : ℝ) ^ length)
  have blockCrossing := critical_block_crossing_lower (blockCount base length) (pathCount length) (length - 2)
    blocksPositive _ interval.1 interval.2 fixedPoint
  simp only [Nat.sub_add_cancel lengthAtLeastTwo] at blockCrossing
  have inverseBound := conditionalStatusWeight_inverse_mean_upper (pathCount length) pathsPositive
    (appendixCriticalProbability base length ^ length) (by positivity) (pow_le_one₀ positive.le belowOne.le) (by linarith)
  have logarithmPositive : 0 < Real.log base := Real.log_pos baseAboveOne
  have meanPositive : 0 < (pathCount length : ℝ) * appendixCriticalProbability base length ^ length := by positivity
  have scalarBound : (length : ℝ) * (4 / ((pathCount length : ℝ) * appendixCriticalProbability base length ^ length)) <
      8 / Real.log base := by
    apply (lt_div_iff₀ logarithmPositive).mpr
    have quotient : (length : ℝ) * (4 / ((pathCount length : ℝ) * appendixCriticalProbability base length ^ length)) * Real.log base =
        (4 * (length : ℝ) * Real.log base) / ((pathCount length : ℝ) * appendixCriticalProbability base length ^ length) := by ring
    rw [quotient]
    apply (div_lt_iff₀ meanPositive).mpr
    nlinarith [meanBounds.1]
  exact (mul_le_mul_of_nonneg_left inverseBound (Nat.cast_nonneg length)).trans_lt scalarBound

end
end IGSIII4.SpectralDensity.ActualFamily
