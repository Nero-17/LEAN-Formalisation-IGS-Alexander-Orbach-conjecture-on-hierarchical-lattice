import IGSIII4.SpectralDensity.ActualUnitInputUpper

/-! The unit-input block bound and the sharper whole-cell upper bound
before the additive constant is absorbed into the exponential factor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability Filter Topology
open scoped BigOperators

theorem appendix_actualBlock_unit_mean_upper_eventually
    {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (base : ℝ) (baseAboveOne : 1 < base) (weight : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) :
    ∀ᶠ length : ℕ in atTop,
      actualBlockObservable (pathCount length) length (appendixCriticalProbability base length)
        weight (fun _ => 1) id < 8 / Real.log base := by
  filter_upwards [appendix_conditional_inverse_upper_eventually base baseAboveOne] with length inverseBound
  rw [actualBlock_unit_mean _ _ _ weight normalized]
  exact inverseBound

theorem appendix_weightedCell_unit_mean_sharp_upper
    {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (base : ℝ) (baseAboveOne : 1 < base) (weight : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1) :
    ∀ᶠ length : ℕ in atTop,
      weightedCellMean (blockCount base length) (pathCount length) (length - 2)
        (appendixCriticalProbability base length) weight (fun _ => 1) <
          2 + 8 * (blockCount base length : ℝ) / Real.log base := by
  filter_upwards [appendix_conditional_inverse_upper_eventually base baseAboveOne,
    appendixCriticalProbability_interval_eventually base baseAboveOne,
    eventually_ge_atTop (2 : ℕ)] with length inverseBound interval lengthLarge
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthLarge
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have blocksRealPositive : 0 < (blockCount base length : ℝ) := Nat.cast_pos.mpr blocksPositive
  have blockCrossing := critical_block_crossing_lower (blockCount base length) (pathCount length) (length - 2)
    blocksPositive _ interval.1 interval.2 fixedPoint
  simp only [Nat.sub_add_cancel lengthLarge] at blockCrossing
  have crossingPositive : 0 < 1 - (1 - appendixCriticalProbability base length ^ length) ^ pathCount length := by
    linarith
  have upper := weightedCell_unit_mean_upper (blockCount base length) (pathCount length) (length - 2)
    (appendixCriticalProbability base length) positive belowOne.le fixedPoint
    (by simpa only [Nat.sub_add_cancel lengthLarge] using crossingPositive) weight nonnegative normalized
  simp only [Nat.sub_add_cancel lengthLarge] at upper
  have inverseNonnegative : 0 ≤ finiteMean
      (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
      (fun success => 1 / (successCount (pathCount length) success : ℝ)) := by
    apply Finset.sum_nonneg
    intro success _
    apply mul_nonneg
    · exact conditionalStatusWeight_nonnegative (pathCount length) _ (pow_nonneg positive.le length)
        (pow_le_one₀ positive.le belowOne.le) crossingPositive success
    · positivity
  have scaledNonnegative : 0 ≤ (blockCount base length : ℝ) * (length : ℝ) * finiteMean
      (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
      (fun success => 1 / (successCount (pathCount length) success : ℝ)) := by positivity
  have sharpened := mul_lt_mul_of_pos_left inverseBound blocksRealPositive
  have routingUpper : weightedCellMean (blockCount base length) (pathCount length) (length - 2)
        (appendixCriticalProbability base length) weight (fun _ => 1) ≤
      2 + (blockCount base length : ℝ) * ((length : ℝ) * finiteMean
        (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
        (fun success => 1 / (successCount (pathCount length) success : ℝ))) := by
    nlinarith [mul_nonneg positive.le scaledNonnegative]
  have identity : (blockCount base length : ℝ) * (8 / Real.log base) =
      8 * (blockCount base length : ℝ) / Real.log base := by ring
  rw [identity] at sharpened
  linarith

end
end IGSIII4.SpectralDensity.ActualFamily
