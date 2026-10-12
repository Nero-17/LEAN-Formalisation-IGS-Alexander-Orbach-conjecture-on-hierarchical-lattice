import IGSIII4.SpectralDensity.ActualProbability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

theorem chain_probability_mono (blocks paths length : ℕ) {first second : ℝ}
    (firstNonnegative : 0 ≤ first) (ordered : first ≤ second) (secondBelowOne : second ≤ 1) :
    (1 - (1 - first ^ length) ^ paths) ^ blocks ≤
      (1 - (1 - second ^ length) ^ paths) ^ blocks := by
  have secondNonnegative := firstNonnegative.trans ordered
  have powers := pow_le_pow_left₀ firstNonnegative ordered length
  have secondPowerBelowOne := pow_le_one₀ (n := length) secondNonnegative secondBelowOne
  have firstPowerBelowOne := powers.trans secondPowerBelowOne
  have failurePowers := pow_le_pow_left₀ (sub_nonneg.mpr secondPowerBelowOne)
    (show 1 - second ^ length ≤ 1 - first ^ length by linarith) paths
  have firstFailureBelowOne := pow_le_one₀ (n := paths) (sub_nonneg.mpr firstPowerBelowOne)
    (show 1 - first ^ length ≤ 1 by linarith [pow_nonneg firstNonnegative length])
  exact pow_le_pow_left₀ (sub_nonneg.mpr firstFailureBelowOne)
    (show 1 - (1 - first ^ length) ^ paths ≤ 1 - (1 - second ^ length) ^ paths by linarith) blocks

/-- Numerical endpoint tests locate every interior fixed point of the actual graph. -/
theorem critical_interval_from_endpoint_tests (blocks paths interior : ℕ) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : (network blocks paths interior).reliability probability = probability)
    (lowerTest : (1 - (1 - (7 / 10 : ℝ) ^ (interior + 2)) ^ paths) ^ blocks < 100 / 119)
    (upperTest : 25 / 36 < (1 - (1 - (4 / 5 : ℝ) ^ (interior + 2)) ^ paths) ^ blocks) :
    7 / 10 < probability ∧ probability < 4 / 5 := by
  have critical := actual_critical_equation blocks paths interior probability positive belowOne fixedPoint
  have denominatorPositive : 0 < probability * (1 + probability) := by positivity
  have identity : (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks *
      (probability * (1 + probability)) = 1 := (eq_div_iff denominatorPositive.ne').mp critical
  have crossingNonnegative : 0 ≤ (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks := by
    rw [critical]
    positivity
  constructor
  · by_contra notAbove
    have ordered : probability ≤ 7 / 10 := le_of_not_gt notAbove
    have crossingBound := (chain_probability_mono blocks paths (interior + 2) positive.le ordered
      (by norm_num : (7 / 10 : ℝ) ≤ 1)).trans_lt lowerTest
    have denominatorBound : probability * (1 + probability) ≤ 119 / 100 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left denominatorBound crossingNonnegative]
  · by_contra notBelow
    have ordered : (4 / 5 : ℝ) ≤ probability := le_of_not_gt notBelow
    have crossingBound := upperTest.trans_le
      (chain_probability_mono blocks paths (interior + 2) (by norm_num) ordered belowOne.le)
    have denominatorBound : (36 / 25 : ℝ) ≤ probability * (1 + probability) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left denominatorBound crossingNonnegative]

end
end IGSIII4.SpectralDensity.ActualFamily
