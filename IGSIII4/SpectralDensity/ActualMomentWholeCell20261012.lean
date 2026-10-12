import IGSIII4.SpectralDensity.ActualMomentCellComparison20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability
attribute [local instance] Classical.propDecidable

theorem chainWeight_nonnegative20261012 (blocks paths length : ℕ) (probability : ℝ)
    (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1)
    (configuration : Fin blocks → Fin paths → Configuration length) :
    0 ≤ chainWeight blocks paths length probability configuration := by
  apply Finset.prod_nonneg
  intro block _
  apply Finset.prod_nonneg
  intro path _
  exact bernoulliWeight_nonneg nonnegative atMostOne _

theorem critical_long_only_coefficient20261012 (blocks paths interior : ℕ) (probability : ℝ)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) :
    (1 - probability ^ 2) * probability ^ 2 * (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks =
      probability * (1 - probability) := by
  rw [reliability_formula] at fixedPoint
  nlinarith [fixedPoint]

theorem weightedCell_mean_lower_long20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths interior : ℕ) (probability : ℝ) (probabilityPositive : 0 < probability)
    (probabilityAtMostOne : probability ≤ 1)
    (fixedPoint : (network blocks paths interior).reliability probability = probability)
    (crossingPositive : 0 < 1 - (1 - probability ^ (interior + 2)) ^ paths)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome) :
    (1 - probability) * finiteMean (actualLongWeight blocks paths (interior + 2) probability weight)
      (actualLongResponse blocks paths (interior + 2) response) ≤
        weightedCellMean blocks paths interior probability weight response := by
  unfold weightedCellMean
  rw [weightedCellObservable_split20261012 blocks paths interior probability fixedPoint weight response positive id]
  apply (le_div_iff₀ probabilityPositive).mpr
  have comparison :
      (∑ configuration : Fin blocks → Fin paths → Configuration (interior + 2),
        chainWeight blocks paths (interior + 2) probability configuration *
          Universality.FiniteNetwork.expectation probability (fun outer =>
            if OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration) outer then
              rawLongObservable blocks paths (interior + 2) configuration weight response id else 0)) ≤
      ∑ configuration : Fin blocks → Fin paths → Configuration (interior + 2),
        chainWeight blocks paths (interior + 2) probability configuration *
          Universality.FiniteNetwork.expectation probability (fun outer =>
            maskedCircuitMoment blocks paths interior (outer,configuration) weight response id) := by
    apply Finset.sum_le_sum
    intro configuration _
    apply mul_le_mul_of_nonneg_left _ (chainWeight_nonnegative20261012 blocks paths (interior + 2) probability probabilityPositive.le probabilityAtMostOne configuration)
    exact finiteMean_mono (bernoulliWeight probability) (bernoulliWeight_nonneg probabilityPositive.le probabilityAtMostOne)
      (fun outer => maskedCircuitMoment_mean_lower20261012 (outer, configuration) weight response weightNonnegative positive)
  rw [actual_long_only_observable20261012 blocks paths (interior + 2) probability crossingPositive weight response normalized id,
    critical_long_only_coefficient20261012 blocks paths interior probability fixedPoint] at comparison
  simp only [id_eq] at comparison
  change ((1 - probability) * finiteMean (actualLongWeight blocks paths (interior + 2) probability weight)
    (actualLongResponse blocks paths (interior + 2) response)) * probability ≤ _
  convert comparison using 1 <;> first | rfl | ring

theorem weightedCell_second_upper_long20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths interior : ℕ) (probability : ℝ) (probabilityPositive : 0 < probability)
    (probabilityAtMostOne : probability ≤ 1)
    (fixedPoint : (network blocks paths interior).reliability probability = probability)
    (crossingPositive : 0 < 1 - (1 - probability ^ (interior + 2)) ^ paths)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    weightedCellSecondMoment blocks paths interior probability weight response ≤
      20 * probability + (1 - probability) *
        finiteMean (actualLongWeight blocks paths (interior + 2) probability weight)
          (fun input => actualLongResponse blocks paths (interior + 2) response input ^ 2) := by
  unfold weightedCellSecondMoment
  rw [weightedCellObservable_split20261012 blocks paths interior probability fixedPoint weight response positive (fun value => value ^ 2)]
  apply (div_le_iff₀ probabilityPositive).mpr
  have comparison :
      (∑ configuration : Fin blocks → Fin paths → Configuration (interior + 2),
        chainWeight blocks paths (interior + 2) probability configuration *
          Universality.FiniteNetwork.expectation probability (fun outer =>
            maskedCircuitMoment blocks paths interior (outer,configuration) weight response (fun value => value ^ 2))) ≤
      ∑ configuration : Fin blocks → Fin paths → Configuration (interior + 2),
        chainWeight blocks paths (interior + 2) probability configuration *
          Universality.FiniteNetwork.expectation probability (fun outer =>
            (if OuterShort outer then 20 else 0) +
              (if OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration) outer then
                rawLongObservable blocks paths (interior + 2) configuration weight response (fun value => value ^ 2) else 0)) := by
    apply Finset.sum_le_sum
    intro configuration _
    apply mul_le_mul_of_nonneg_left _ (chainWeight_nonnegative20261012 blocks paths (interior + 2) probability probabilityPositive.le probabilityAtMostOne configuration)
    exact finiteMean_mono (bernoulliWeight probability) (bernoulliWeight_nonneg probabilityPositive.le probabilityAtMostOne)
      (fun outer => maskedCircuitMoment_second_upper20261012 (outer,configuration) weight response weightNonnegative normalized positive meanOne varianceBound)
  have shortExpectation : Universality.FiniteNetwork.expectation probability (fun outer : Configuration 4 => if OuterShort outer then 20 else 0) =
      20 * probability ^ 2 := by
    have identity : (fun outer : Configuration 4 => if OuterShort outer then (20 : ℝ) else 0) =
        (fun outer => 20 * (if OuterShort outer then 1 else 0)) := by funext outer; split_ifs <;> ring
    rw [identity, Universality.FiniteNetwork.expectation_const_mul, outer_short_probability20261012]
  simp only [Universality.FiniteNetwork.expectation_add, shortExpectation, mul_add, Finset.sum_add_distrib] at comparison
  rw [← Finset.sum_mul, chain_weight_normalization, one_mul,
    actual_long_only_observable20261012 blocks paths (interior + 2) probability crossingPositive weight response normalized (fun value => value ^ 2),
    critical_long_only_coefficient20261012 blocks paths interior probability fixedPoint] at comparison
  convert comparison using 1 <;> first | rfl | ring

theorem weightedCell_second_upper_long_variance20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths interior : ℕ) (probability : ℝ) (probabilityPositive : 0 < probability)
    (probabilityAtMostOne : probability ≤ 1)
    (fixedPoint : (network blocks paths interior).reliability probability = probability)
    (crossingPositive : 0 < 1 - (1 - probability ^ (interior + 2)) ^ paths)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    weightedCellSecondMoment blocks paths interior probability weight response ≤
      20 * probability + (1 - probability) *
        ((finiteMean (actualLongWeight blocks paths (interior + 2) probability weight)
          (actualLongResponse blocks paths (interior + 2) response)) ^ 2 +
            16 + (blocks : ℝ) * (((interior + 2 : ℕ) : ℝ) ^ 2 + 8 * (interior + 2 : ℕ))) := by
  apply (weightedCell_second_upper_long20261012 blocks paths interior probability probabilityPositive probabilityAtMostOne fixedPoint crossingPositive
    weight response weightNonnegative normalized positive meanOne varianceBound).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr probabilityAtMostOne)
  exact actualLong_second_moment_bound20261012 blocks paths (interior + 2) probability probabilityPositive.le probabilityAtMostOne crossingPositive
    weight response weightNonnegative normalized positive (by omega) meanOne varianceBound

end
end IGSIII4.SpectralDensity.ActualFamily
