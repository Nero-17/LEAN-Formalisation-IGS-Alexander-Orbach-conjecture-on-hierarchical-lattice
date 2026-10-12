import IGSIII4.SpectralDensity.ActualBinomialReciprocal
import IGSIII4.SpectralDensity.ActualBinomialEstimates
import IGSIII34.Probability.FiniteTensorization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork Filter Topology
open IGSIII34.Probability (finiteMean)
open scoped BigOperators

def conditionalStatusWeight (paths : ℕ) (probability : ℝ) (configuration : Configuration paths) : ℝ :=
  if 0 < successCount paths configuration then
    bernoulliWeight probability configuration / (1 - (1 - probability) ^ paths) else 0

theorem conditionalStatusWeight_expectation (paths : ℕ) (probability : ℝ)
    (response : Configuration paths → ℝ) :
    finiteMean (conditionalStatusWeight paths probability) response =
      expectation probability (fun configuration =>
        if 0 < successCount paths configuration then response configuration else 0) /
          (1 - (1 - probability) ^ paths) := by
  unfold finiteMean conditionalStatusWeight expectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases positive : 0 < successCount paths configuration <;> simp [positive, div_mul_eq_mul_div]

theorem conditionalStatusWeight_normalized (paths : ℕ) (probability : ℝ)
    (crossingPositive : 0 < 1 - (1 - probability) ^ paths) :
    (∑ configuration, conditionalStatusWeight paths probability configuration) = 1 := by
  have identity := conditionalStatusWeight_expectation paths probability (fun _ => 1)
  simp only [finiteMean, mul_one] at identity
  rw [successCount_positive_probability] at identity
  simpa only [div_self crossingPositive.ne'] using identity

theorem conditionalStatusWeight_nonnegative (paths : ℕ) (probability : ℝ)
    (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1)
    (crossingPositive : 0 < 1 - (1 - probability) ^ paths)
    (configuration : Configuration paths) : 0 ≤ conditionalStatusWeight paths probability configuration := by
  unfold conditionalStatusWeight
  split_ifs
  · exact div_nonneg (bernoulliWeight_nonneg nonnegative atMostOne _) crossingPositive.le
  · rfl

theorem conditionalStatusWeight_zero (paths : ℕ) (probability : ℝ)
    (configuration : Configuration paths) (failed : ¬ ∃ path, configuration path = true) :
    conditionalStatusWeight paths probability configuration = 0 := by
  unfold conditionalStatusWeight
  rw [if_neg]
  rwa [successCount_positive_iff]

theorem conditionalStatusWeight_count_mean (paths : ℕ) (probability : ℝ) :
    finiteMean (conditionalStatusWeight paths probability)
      (fun configuration => (successCount paths configuration : ℝ)) =
        (paths : ℝ) * probability / (1 - (1 - probability) ^ paths) := by
  rw [conditionalStatusWeight_expectation]
  have indicator (configuration : Configuration paths) :
      (if 0 < successCount paths configuration then (successCount paths configuration : ℝ) else 0) =
        (successCount paths configuration : ℝ) := by
    split_ifs with positive
    · rfl
    · have zero : successCount paths configuration = 0 := by omega
      simp [zero]
  simp_rw [indicator]
  rw [successCount_mean]

theorem conditionalStatusWeight_inverse_mean_upper (paths : ℕ) (pathsPositive : 0 < paths)
    (probability : ℝ) (positive : 0 < probability) (atMostOne : probability ≤ 1)
    (crossingLarge : 1 / 2 < 1 - (1 - probability) ^ paths) :
    finiteMean (conditionalStatusWeight paths probability)
      (fun configuration => 1 / (successCount paths configuration : ℝ)) ≤ 4 / ((paths : ℝ) * probability) := by
  rw [conditionalStatusWeight_expectation]
  exact binomial_reciprocal_conditional_bound paths pathsPositive probability positive atMostOne crossingLarge

/-- The reciprocal mean lower bound follows from a finite tangent inequality. -/
theorem finite_status_inverse_mean_lower (paths : ℕ) (weight : Configuration paths → ℝ)
    (nonnegative : ∀ configuration, 0 ≤ weight configuration)
    (normalized : ∑ configuration, weight configuration = 1)
    (zeroOnFailure : ∀ configuration, ¬ (∃ path, configuration path = true) → weight configuration = 0)
    (upper : ℝ) (upperPositive : 0 < upper)
    (meanBound : finiteMean weight (fun configuration => (successCount paths configuration : ℝ)) ≤ upper) :
    1 / upper ≤ finiteMean weight (fun configuration => 1 / (successCount paths configuration : ℝ)) := by
  have pointwise (configuration : Configuration paths) :
      weight configuration * (2 / upper - (successCount paths configuration : ℝ) / upper ^ 2) ≤
        weight configuration * (1 / (successCount paths configuration : ℝ)) := by
    by_cases positive : 0 < successCount paths configuration
    · apply mul_le_mul_of_nonneg_left _ (nonnegative configuration)
      have countRealPositive : 0 < (successCount paths configuration : ℝ) := by exact_mod_cast positive
      have tangent : 2 / upper - (successCount paths configuration : ℝ) / upper ^ 2 ≤
          1 / (successCount paths configuration : ℝ) := by
        apply (le_div_iff₀ countRealPositive).mpr
        have square := sq_nonneg ((successCount paths configuration : ℝ) - upper)
        field_simp
        nlinarith
      exact tangent
    · have failed : ¬ (∃ path, configuration path = true) := by
        rwa [← successCount_positive_iff]
      rw [zeroOnFailure configuration failed]
      simp
  have comparison := Finset.sum_le_sum (fun configuration (_ : configuration ∈ Finset.univ) => pointwise configuration)
  have leftSum : (∑ configuration, weight configuration *
        (2 / upper - (successCount paths configuration : ℝ) / upper ^ 2)) =
      2 / upper - finiteMean weight (fun configuration => (successCount paths configuration : ℝ)) / upper ^ 2 := by
    simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, finiteMean, normalized, one_mul]
  rw [leftSum] at comparison
  change _ ≤ finiteMean weight (fun configuration => 1 / (successCount paths configuration : ℝ)) at comparison
  have meanDivisionBound := div_le_div_of_nonneg_right meanBound (sq_nonneg upper)
  have cancellation : upper / upper ^ 2 = 1 / upper := by field_simp
  rw [cancellation] at meanDivisionBound
  have twoDivide : 2 / upper = 2 * (1 / upper) := by ring
  rw [twoDivide] at comparison
  linarith

theorem critical_block_crossing_lower (blocks paths interior : ℕ) (blocksPositive : 0 < blocks)
    (probability : ℝ) (above : 7 / 10 < probability) (below : probability < 4 / 5)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) :
    25 / 36 < 1 - (1 - probability ^ (interior + 2)) ^ paths := by
  have positive : 0 < probability := by linarith
  have powerAtMostOne : probability ^ (interior + 2) ≤ 1 := pow_le_one₀ positive.le (by linarith)
  have failureNonnegative : 0 ≤ (1 - probability ^ (interior + 2)) ^ paths := by positivity
  have failureAtMostOne : (1 - probability ^ (interior + 2)) ^ paths ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith [pow_nonneg positive.le (interior + 2)])
  have chainBound := unit_interval_power_le_self (1 - (1 - probability ^ (interior + 2)) ^ paths)
    (by linarith) (by linarith) blocks blocksPositive
  exact (critical_chain_probability_interval blocks paths interior probability above below fixedPoint).1.trans_le chainBound

theorem appendix_conditional_count_and_inverse_bounds_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      finiteMean (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
        (fun configuration => (successCount (pathCount length) configuration : ℝ)) <
          2 * ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ) ∧
      1 / (2 * ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ)) ≤
        finiteMean (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
          (fun configuration => 1 / (successCount (pathCount length) configuration : ℝ)) := by
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    appendix_success_mean_bounds_eventually base baseAboveOne, eventually_ge_atTop (4 : ℕ)] with length interval meanBounds lengthLarge
  have lengthAtLeastTwo : 2 ≤ length := by omega
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthAtLeastTwo
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have blockCrossing := critical_block_crossing_lower (blockCount base length) (pathCount length) (length - 2)
    blocksPositive _ interval.1 interval.2 fixedPoint
  simp only [Nat.sub_add_cancel lengthAtLeastTwo] at blockCrossing
  have crossingPositive : 0 < 1 - (1 - appendixCriticalProbability base length ^ length) ^ pathCount length := by linarith
  have upperPositive : 0 < 2 * ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ) := by positivity
  have conditionalMeanBound : finiteMean (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
      (fun configuration => (successCount (pathCount length) configuration : ℝ)) <
        2 * ((⌈base⌉₊ : ℝ) + 2) * (length : ℝ) := by
    rw [conditionalStatusWeight_count_mean]
    apply (div_lt_iff₀ crossingPositive).mpr
    nlinarith [meanBounds.2]
  refine ⟨conditionalMeanBound, ?_⟩
  apply finite_status_inverse_mean_lower (pathCount length)
    (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
    (conditionalStatusWeight_nonnegative _ _ (by positivity) (pow_le_one₀ positive.le belowOne.le) crossingPositive)
    (conditionalStatusWeight_normalized _ _ crossingPositive)
    (conditionalStatusWeight_zero _ _) _ upperPositive conditionalMeanBound.le

end
end IGSIII4.SpectralDensity.ActualFamily
