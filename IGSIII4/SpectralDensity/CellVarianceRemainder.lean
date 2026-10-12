import IGSIII4.SpectralDensity.StrictCellMoments
import IGSIII4.SpectralDensity.MixtureVarianceRemainder
import IGSIII4.SpectralDensity.WeightedCellVariance

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability Filter Topology
attribute [local instance] Classical.propDecidable

theorem finite_cell_variance_remainder_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      ∀ {Outcome : Type} [Fintype Outcome] [Nonempty Outcome]
        (weight response : Outcome → ℝ),
        (∀ outcome, 0 ≤ weight outcome) → (∑ outcome, weight outcome = 1) →
        (∀ outcome, 0 < response outcome) → finiteMean weight response = 1 →
        finiteVariance weight response ≤ 8 →
        weightedCellObservable (blockCount base length) (pathCount length) (length - 2)
            (appendixCriticalProbability base length) weight response
            (fun value => (value - weightedCellMean (blockCount base length) (pathCount length)
              (length - 2) (appendixCriticalProbability base length) weight response) ^ 2) /
          weightedCellMean (blockCount base length) (pathCount length) (length - 2)
            (appendixCriticalProbability base length) weight response ^ 2 <
          4 + 1600 * ((⌈base⌉₊ : ℝ) + 2) ^ 2 *
            ((length : ℝ) ^ 2 + 8 * length + 36) / (blockCount base length : ℝ) ∧
        4 + 1600 * ((⌈base⌉₊ : ℝ) + 2) ^ 2 *
            ((length : ℝ) ^ 2 + 8 * length + 36) / (blockCount base length : ℝ) < 8 := by
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    appendix_conditional_count_and_inverse_bounds_eventually base baseAboveOne,
    path_tail_remainder_relative_eventually_small ((⌈base⌉₊ : ℝ) + 2),
    variance_remainder_eventually_small base baseAboveOne ((⌈base⌉₊ : ℝ) + 2),
    eventually_ge_atTop (4 : ℕ)] with length interval inverseBounds tailSmall cutoff lengthLarge
  have lengthAtLeastTwo : 2 ≤ length := by omega
  have lengthPositive : 0 < length := by omega
  have lengthIdentity : length - 2 + 2 = length := Nat.sub_add_cancel lengthAtLeastTwo
  have constantPositive : 0 < (⌈base⌉₊ : ℝ) + 2 := by positivity
  obtain ⟨probabilityPositive, probabilityBelowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthAtLeastTwo
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have blocksAboveOne : 1 ≤ (blockCount base length : ℝ) := by
    exact_mod_cast (show 1 ≤ blockCount base length from blocksPositive)
  have blockCrossing := critical_block_crossing_lower (blockCount base length) (pathCount length) (length - 2)
    blocksPositive (appendixCriticalProbability base length) interval.1 interval.2 fixedPoint
  rw [lengthIdentity] at blockCrossing
  have crossingPositive : 0 < 1 - (1 - appendixCriticalProbability base length ^ length) ^ pathCount length := by linarith
  intro Outcome _ _ weight response weightNonnegative normalized positive meanOne varianceBound
  have blockLower := actualBlock_mean_uniform_lower (pathCount length) length
    (appendixCriticalProbability base length) ((⌈base⌉₊ : ℝ) + 2) constantPositive lengthPositive
    probabilityPositive.le probabilityBelowOne.le crossingPositive inverseBounds.2 tailSmall
    weight response weightNonnegative normalized positive meanOne varianceBound
  have longMean := actualLong_mean (blockCount base length) (pathCount length) length
    (appendixCriticalProbability base length) crossingPositive weight response normalized meanOne
  have longLower : (blockCount base length : ℝ) / (8 * ((⌈base⌉₊ : ℝ) + 2)) ≤
      finiteMean (actualLongWeight (blockCount base length) (pathCount length) length
        (appendixCriticalProbability base length) weight)
        (actualLongResponse (blockCount base length) (pathCount length) length response) := by
    rw [longMean]
    have scaled := mul_le_mul_of_nonneg_left blockLower (Nat.cast_nonneg (blockCount base length))
    have identity : (blockCount base length : ℝ) * (1 / (8 * ((⌈base⌉₊ : ℝ) + 2))) =
        (blockCount base length : ℝ) / (8 * ((⌈base⌉₊ : ℝ) + 2)) := by ring
    rw [identity] at scaled
    linarith
  have meanLower := weightedCell_mean_lower_long (blockCount base length) (pathCount length) (length - 2)
    (appendixCriticalProbability base length) probabilityPositive probabilityBelowOne.le fixedPoint
    (by simpa only [lengthIdentity] using crossingPositive) weight response weightNonnegative normalized positive
  have secondUpper := weightedCell_second_upper_long_variance (blockCount base length) (pathCount length) (length - 2)
    (appendixCriticalProbability base length) probabilityPositive probabilityBelowOne.le fixedPoint
    (by simpa only [lengthIdentity] using crossingPositive) weight response weightNonnegative normalized positive meanOne varianceBound
  change (1 - appendixCriticalProbability base length) * actualLongMean (blockCount base length) (pathCount length)
    (length - 2 + 2) (appendixCriticalProbability base length) weight response ≤
      weightedCellMean (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response at meanLower
  change weightedCellSecondMoment (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response ≤
    20 * appendixCriticalProbability base length + (1 - appendixCriticalProbability base length) *
      (actualLongMean (blockCount base length) (pathCount length) (length - 2 + 2)
        (appendixCriticalProbability base length) weight response ^ 2 + 16 +
          (blockCount base length : ℝ) * (((length - 2 + 2 : ℕ) : ℝ) ^ 2 + 8 * (length - 2 + 2 : ℕ))) at secondUpper
  rw [lengthIdentity] at meanLower secondUpper
  have result := mixture_normalized_variance_remainder (blockCount base length : ℝ) ((⌈base⌉₊ : ℝ) + 2)
    ((length : ℝ) ^ 2 + 8 * length) (appendixCriticalProbability base length)
    (finiteMean (actualLongWeight (blockCount base length) (pathCount length) length
      (appendixCriticalProbability base length) weight)
      (actualLongResponse (blockCount base length) (pathCount length) length response))
    (weightedCellMean (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response)
    (weightedCellSecondMoment (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response)
    blocksAboveOne constantPositive (by positivity) probabilityPositive.le interval.2 longLower meanLower secondUpper
  rw [weightedCell_centered_second_moment (blockCount base length) (pathCount length)
    (length - 2) (appendixCriticalProbability base length) probabilityPositive probabilityBelowOne
    fixedPoint weight response normalized]
  exact ⟨result, by linarith [cutoff]⟩

end
end IGSIII4.SpectralDensity.ActualFamily
