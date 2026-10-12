import IGSIII4.SpectralDensity.ActualMomentUniformInvariant

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability Filter Topology

theorem finite_status_inverse_mean_strict_lower (paths : ℕ)
    (weight : Configuration paths → ℝ)
    (nonnegative : ∀ configuration, 0 ≤ weight configuration)
    (normalized : ∑ configuration, weight configuration = 1)
    (zeroOnFailure : ∀ configuration, ¬ (∃ path, configuration path = true) →
      weight configuration = 0)
    (upper : ℝ) (upperPositive : 0 < upper)
    (meanBound : finiteMean weight (fun configuration =>
      (successCount paths configuration : ℝ)) < upper) :
    1 / upper < finiteMean weight (fun configuration =>
      1 / (successCount paths configuration : ℝ)) := by
  have meanNonnegative : 0 ≤ finiteMean weight (fun configuration =>
      (successCount paths configuration : ℝ)) := by
    exact Finset.sum_nonneg (fun configuration _ =>
      mul_nonneg (nonnegative configuration) (Nat.cast_nonneg _))
  have midpointPositive : 0 <
      (finiteMean weight (fun configuration => (successCount paths configuration : ℝ)) + upper) / 2 :=
    by linarith
  have midpointBelow :
      (finiteMean weight (fun configuration => (successCount paths configuration : ℝ)) + upper) / 2 < upper :=
    by linarith
  exact (one_div_lt_one_div_of_lt midpointPositive midpointBelow).trans_le
    (finite_status_inverse_mean_lower paths weight nonnegative normalized zeroOnFailure
      _ midpointPositive (by linarith))

theorem actualBlock_mean_strict_lower {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability constant : ℝ) (constantPositive : 0 < constant)
    (lengthPositive : 0 < length) (probabilityNonnegative : 0 ≤ probability)
    (probabilityAtMostOne : probability ≤ 1)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (inverseLower : 1 / (2 * constant * (length : ℝ)) <
      finiteMean (conditionalStatusWeight paths (probability ^ length))
        (fun configuration => 1 / (successCount paths configuration : ℝ)))
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    1 / (4 * constant) - (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length <
      actualBlockObservable paths length probability weight response id := by
  have lengthRealPositive : 0 < (length : ℝ) := Nat.cast_pos.mpr lengthPositive
  have scaledInverse := mul_lt_mul_of_pos_left inverseLower
    (show 0 < (length : ℝ) / 2 by positivity)
  have cancellation : (length : ℝ) / 2 * (1 / (2 * constant * (length : ℝ))) =
      1 / (4 * constant) := by
    field_simp [ne_of_gt constantPositive, ne_of_gt lengthRealPositive]
    ring
  rw [cancellation] at scaledInverse
  have blockLower := actualBlock_mean_lower paths length probability probabilityNonnegative
    probabilityAtMostOne crossingPositive weight response weightNonnegative normalized positive
    lengthPositive meanOne varianceBound
  linarith

theorem actualBlock_mean_uniform_strict_lower {Outcome : Type*}
    [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability constant : ℝ) (constantPositive : 0 < constant)
    (lengthPositive : 0 < length) (probabilityNonnegative : 0 ≤ probability)
    (probabilityAtMostOne : probability ≤ 1)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (inverseLower : 1 / (2 * constant * (length : ℝ)) ≤
      finiteMean (conditionalStatusWeight paths (probability ^ length))
        (fun configuration => 1 / (successCount paths configuration : ℝ)))
    (tailSmall : 4 * constant * (length : ℝ) * (69 / 70 : ℝ) ^ length < 1)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    1 / (8 * constant) < actualBlockObservable paths length probability weight response id := by
  have lengthRealPositive : 0 < (length : ℝ) := Nat.cast_pos.mpr lengthPositive
  have scaledInverse := mul_le_mul_of_nonneg_left inverseLower
    (show 0 ≤ (length : ℝ) / 2 by positivity)
  have cancellation : (length : ℝ) / 2 * (1 / (2 * constant * (length : ℝ))) =
      1 / (4 * constant) := by
    field_simp [ne_of_gt constantPositive, ne_of_gt lengthRealPositive]
    ring
  rw [cancellation] at scaledInverse
  have tailBound : (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length < 1 / (8 * constant) := by
    apply (lt_div_iff₀ (by positivity : 0 < 8 * constant)).mpr
    nlinarith [tailSmall]
  have blockLower := actualBlock_mean_lower paths length probability probabilityNonnegative
    probabilityAtMostOne crossingPositive weight response weightNonnegative normalized positive
    lengthPositive meanOne varianceBound
  have reciprocal : 1 / (4 * constant) = 2 * (1 / (8 * constant)) := by ring
  rw [reciprocal] at scaledInverse
  linarith

theorem actualLong_mean_uniform_strict_lower {Outcome : Type*}
    [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability constant : ℝ)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1)
    (meanOne : finiteMean weight response = 1)
    (blockLower : 1 / (8 * constant) ≤ actualBlockObservable paths length probability weight response id) :
    (blocks : ℝ) / (8 * constant) <
      finiteMean (actualLongWeight blocks paths length probability weight)
        (actualLongResponse blocks paths length response) := by
  rw [actualLong_mean blocks paths length probability crossingPositive weight response normalized meanOne]
  have scaled := mul_le_mul_of_nonneg_left blockLower (Nat.cast_nonneg blocks)
  have cancellation : (blocks : ℝ) * (1 / (8 * constant)) = (blocks : ℝ) / (8 * constant) := by ring
  rw [cancellation] at scaled
  linarith

/-- A graph-only cutoff simultaneously gives the literal strict block and long-branch
mean bounds, and both second-moment estimates, for every finitely supported input law. -/
theorem block_and_long_moment_bounds_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      ∀ {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
        (weight response : Outcome → ℝ),
        (∀ outcome, 0 ≤ weight outcome) → (∑ outcome, weight outcome = 1) →
        (∀ outcome, 0 < response outcome) → finiteMean weight response = 1 →
        finiteVariance weight response ≤ 8 →
        (1 / (4 * ((⌈base⌉₊ : ℝ) + 2)) - (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length <
          actualBlockObservable (pathCount length) length (appendixCriticalProbability base length) weight response id) ∧
        (1 / (8 * ((⌈base⌉₊ : ℝ) + 2)) <
          actualBlockObservable (pathCount length) length (appendixCriticalProbability base length) weight response id) ∧
        (actualBlockObservable (pathCount length) length (appendixCriticalProbability base length)
          weight response (fun value => value ^ 2) ≤ (length : ℝ) ^ 2 + 8 * length) ∧
        ((blockCount base length : ℝ) / (8 * ((⌈base⌉₊ : ℝ) + 2)) <
          finiteMean (actualLongWeight (blockCount base length) (pathCount length) length
            (appendixCriticalProbability base length) weight)
            (actualLongResponse (blockCount base length) (pathCount length) length response)) ∧
        finiteVariance (actualLongWeight (blockCount base length) (pathCount length) length
          (appendixCriticalProbability base length) weight)
          (actualLongResponse (blockCount base length) (pathCount length) length response) ≤
            16 + (blockCount base length : ℝ) * ((length : ℝ) ^ 2 + 8 * length) := by
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    appendix_conditional_count_and_inverse_bounds_eventually base baseAboveOne,
    path_tail_remainder_relative_eventually_small ((⌈base⌉₊ : ℝ) + 2),
    eventually_ge_atTop (4 : ℕ)] with length interval inverseBounds tailSmall lengthLarge
  have lengthAtLeastTwo : 2 ≤ length := by omega
  have lengthPositive : 0 < length := by omega
  have constantPositive : 0 < (⌈base⌉₊ : ℝ) + 2 := by positivity
  obtain ⟨probabilityPositive, probabilityBelowOne, fixedPoint⟩ :=
    appendixCriticalProbability_spec base length lengthAtLeastTwo
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have blockCrossing := critical_block_crossing_lower (blockCount base length) (pathCount length)
    (length - 2) blocksPositive (appendixCriticalProbability base length) interval.1 interval.2 fixedPoint
  rw [Nat.sub_add_cancel lengthAtLeastTwo] at blockCrossing
  have crossingPositive : 0 < 1 - (1 - appendixCriticalProbability base length ^ length) ^ pathCount length := by linarith
  have strictInverse := finite_status_inverse_mean_strict_lower (pathCount length)
    (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
    (conditionalStatusWeight_nonnegative _ _ (by positivity)
      (pow_le_one₀ probabilityPositive.le probabilityBelowOne.le) crossingPositive)
    (conditionalStatusWeight_normalized _ _ crossingPositive)
    (conditionalStatusWeight_zero _ _) _ (by positivity) inverseBounds.1
  intro Outcome _ _ weight response weightNonnegative normalized positive meanOne varianceBound
  have blockLower := actualBlock_mean_uniform_strict_lower (pathCount length) length
    (appendixCriticalProbability base length) ((⌈base⌉₊ : ℝ) + 2) constantPositive lengthPositive
    probabilityPositive.le probabilityBelowOne.le crossingPositive inverseBounds.2 tailSmall
    weight response weightNonnegative normalized positive meanOne varianceBound
  refine ⟨actualBlock_mean_strict_lower (pathCount length) length
    (appendixCriticalProbability base length) ((⌈base⌉₊ : ℝ) + 2) constantPositive lengthPositive
    probabilityPositive.le probabilityBelowOne.le crossingPositive strictInverse weight response
    weightNonnegative normalized positive meanOne varianceBound, blockLower, ?_, ?_, ?_⟩
  · exact actualBlock_second_moment (pathCount length) length (appendixCriticalProbability base length)
      probabilityPositive.le probabilityBelowOne.le crossingPositive weight response weightNonnegative
      normalized positive lengthPositive meanOne varianceBound
  · exact actualLong_mean_uniform_strict_lower (blockCount base length) (pathCount length) length
      (appendixCriticalProbability base length) ((⌈base⌉₊ : ℝ) + 2) crossingPositive weight response
      normalized meanOne blockLower.le
  · exact actualLong_variance_bound (blockCount base length) (pathCount length) length
      (appendixCriticalProbability base length) probabilityPositive.le probabilityBelowOne.le
      crossingPositive weight response weightNonnegative normalized positive lengthPositive meanOne varianceBound

end
end IGSIII4.SpectralDensity.ActualFamily
