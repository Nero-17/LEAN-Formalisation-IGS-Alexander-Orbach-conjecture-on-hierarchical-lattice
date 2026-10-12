import IGSIII4.SpectralDensity.ActualMomentWholeCell20261012
import IGSIII4.SpectralDensity.ActualFiniteIteration20261012
import IGSIII4.SpectralDensity.MixtureMomentAlgebra20261012
import IGSIII4.SpectralDensity.MomentCutoff20261012
import IGSIII4.SpectralDensity.MomentTailCutoff20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability Filter Topology
attribute [local instance] Classical.propDecidable

def actualLongMean20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (weight response : Outcome → ℝ) : ℝ :=
  finiteMean (actualLongWeight blocks paths length probability weight) (actualLongResponse blocks paths length response)

theorem actualBlock_mean_uniform_lower20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability constant : ℝ) (constantPositive : 0 < constant)
    (lengthPositive : 0 < length) (probabilityNonnegative : 0 ≤ probability) (probabilityAtMostOne : probability ≤ 1)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (inverseLower : 1 / (2 * constant * (length : ℝ)) ≤
      finiteMean (conditionalStatusWeight paths (probability ^ length)) (fun configuration => 1 / (successCount paths configuration : ℝ)))
    (tailSmall : 4 * constant * (length : ℝ) * (69 / 70 : ℝ) ^ length < 1)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    1 / (8 * constant) ≤ actualBlockObservable paths length probability weight response id := by
  have lengthRealPositive : 0 < (length : ℝ) := Nat.cast_pos.mpr lengthPositive
  have scaledInverse := mul_le_mul_of_nonneg_left inverseLower (show 0 ≤ (length : ℝ) / 2 by positivity)
  have cancellation : (length : ℝ) / 2 * (1 / (2 * constant * (length : ℝ))) = 1 / (4 * constant) := by
    field_simp [ne_of_gt constantPositive, ne_of_gt lengthRealPositive]
    <;> ring
  rw [cancellation] at scaledInverse
  have tailBound : (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length < 1 / (8 * constant) := by
    apply (lt_div_iff₀ (by positivity : 0 < 8 * constant)).mpr
    nlinarith [tailSmall]
  have blockLower := actualBlock_mean_lower20261012 paths length probability probabilityNonnegative probabilityAtMostOne crossingPositive
    weight response weightNonnegative normalized positive lengthPositive meanOne varianceBound
  have reciprocal : 1 / (4 * constant) = 2 * (1 / (8 * constant)) := by ring
  rw [reciprocal] at scaledInverse
  linarith

/-- One cutoff depending only on the graph-family base works for every finite
normalized positive input law, hence for all actual recursive generations. -/
theorem appendix_finite_cell_moment_bounds_eventually20261012 (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      FiniteCellMomentBounds (blockCount base length) (pathCount length) (length - 2)
        (appendixCriticalProbability base length)
        ((blockCount base length : ℝ) / (40 * ((⌈base⌉₊ : ℝ) + 2))) := by
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
  unfold FiniteCellMomentBounds
  intro Outcome _ _ weight response weightNonnegative normalized positive meanOne varianceBound
  have blockLower := actualBlock_mean_uniform_lower20261012 (pathCount length) length
    (appendixCriticalProbability base length) ((⌈base⌉₊ : ℝ) + 2) constantPositive lengthPositive
    probabilityPositive.le probabilityBelowOne.le crossingPositive inverseBounds.2 tailSmall
    weight response weightNonnegative normalized positive meanOne varianceBound
  have longMean := actualLong_mean20261012 (blockCount base length) (pathCount length) length
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
  have meanLower := weightedCell_mean_lower_long20261012 (blockCount base length) (pathCount length) (length - 2)
    (appendixCriticalProbability base length) probabilityPositive probabilityBelowOne.le fixedPoint
    (by simpa only [lengthIdentity] using crossingPositive) weight response weightNonnegative normalized positive
  have secondUpper := weightedCell_second_upper_long_variance20261012 (blockCount base length) (pathCount length) (length - 2)
    (appendixCriticalProbability base length) probabilityPositive probabilityBelowOne.le fixedPoint
    (by simpa only [lengthIdentity] using crossingPositive) weight response weightNonnegative normalized positive meanOne varianceBound
  change (1 - appendixCriticalProbability base length) * actualLongMean20261012 (blockCount base length) (pathCount length)
    (length - 2 + 2) (appendixCriticalProbability base length) weight response ≤
      weightedCellMean (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response at meanLower
  change weightedCellSecondMoment (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response ≤
    20 * appendixCriticalProbability base length + (1 - appendixCriticalProbability base length) *
      (actualLongMean20261012 (blockCount base length) (pathCount length) (length - 2 + 2)
        (appendixCriticalProbability base length) weight response ^ 2 + 16 +
          (blockCount base length : ℝ) * (((length - 2 + 2 : ℕ) : ℝ) ^ 2 + 8 * (length - 2 + 2 : ℕ))) at secondUpper
  rw [lengthIdentity] at meanLower secondUpper
  have result := mixture_mean_and_second_moment_bound (blockCount base length : ℝ) ((⌈base⌉₊ : ℝ) + 2)
    ((length : ℝ) ^ 2 + 8 * length) (appendixCriticalProbability base length)
    (finiteMean (actualLongWeight (blockCount base length) (pathCount length) length
      (appendixCriticalProbability base length) weight)
      (actualLongResponse (blockCount base length) (pathCount length) length response))
    (weightedCellMean (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response)
    (weightedCellSecondMoment (blockCount base length) (pathCount length) (length - 2) (appendixCriticalProbability base length) weight response)
    blocksAboveOne constantPositive (by positivity) probabilityPositive.le interval.2 longLower meanLower secondUpper cutoff
  exact ⟨result.1.le, result.2.le⟩

end
end IGSIII4.SpectralDensity.ActualFamily
