import IGSIII.Chemical.SmallBall.Laplace
import Universality.Probability.FiniteWeightMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Set
open scoped BigOperators

noncomputable section

variable {Outcome : Type*} [Fintype Outcome] [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]

theorem finiteWeight_integral (weight : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (response : Outcome → ℝ) :
    (∫ outcome, response outcome ∂(finiteWeightPMF weight nonnegative normalized).toMeasure) =
      ∑ outcome, weight outcome * response outcome := by
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, finiteWeightPMF_singleton, ENNReal.toReal_ofReal (nonnegative _), smul_eq_mul]

theorem finiteWeight_event (weight : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (predicate : Outcome → Prop) [DecidablePred predicate] :
    (finiteWeightPMF weight nonnegative normalized).toMeasure.real {outcome | predicate outcome} =
      ∑ outcome, weight outcome * (if predicate outcome then 1 else 0) := by
  have measurableEvent : MeasurableSet {outcome | predicate outcome} := (Set.toFinite _).measurableSet
  have equality := integral_indicator_const (μ := (finiteWeightPMF weight nonnegative normalized).toMeasure)
    (1 : ℝ) measurableEvent
  rw [finiteWeight_integral] at equality
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using equality.symm

theorem finite_smallBall_half_le_of_mean_one_second_moment_bound
    (weight value : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (meanOne : ∑ outcome, weight outcome * value outcome = 1)
    {bound : ℝ} (boundPositive : 0 < bound)
    (secondMomentBound : (∑ outcome, weight outcome * value outcome ^ 2) ≤ bound) :
    (∑ outcome, weight outcome * (if value outcome ≤ (1 / 2 : ℝ) then 1 else 0)) ≤
      1 - 1 / (4 * bound) := by
  have comparison := smallBall_half_le_of_mean_one_second_moment_bound
    (finiteWeightPMF weight nonnegative normalized).toMeasure
    (measurable_of_finite value) Integrable.of_finite Integrable.of_finite
    (by rwa [finiteWeight_integral]) boundPositive (by rwa [finiteWeight_integral])
  rwa [finiteWeight_event] at comparison

theorem finite_laplace_le_smallBall (weight value : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (valueNonnegative : ∀ outcome, 0 ≤ value outcome) {parameter : ℝ}
    (parameterNonnegative : 0 ≤ parameter) (cutoff : ℝ) :
    (∑ outcome, weight outcome * Real.exp (-parameter * value outcome)) ≤
      (∑ outcome, weight outcome * (if value outcome ≤ cutoff then 1 else 0)) +
        Real.exp (-parameter * cutoff) := by
  have comparison := laplace_le_smallBall (finiteWeightPMF weight nonnegative normalized).toMeasure
    (measurable_of_finite value) valueNonnegative parameterNonnegative cutoff
  rwa [finiteWeight_integral, finiteWeight_event] at comparison

theorem finite_rpow_le_one_add_power (weight value : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (valueNonnegative : ∀ outcome, 0 ≤ value outcome) {exponent : ℝ} {power : ℕ}
    (exponentNonnegative : 0 ≤ exponent) (exponentBound : exponent ≤ power) :
    (∑ outcome, weight outcome * value outcome ^ exponent) ≤
      1 + ∑ outcome, weight outcome * value outcome ^ power := by
  have comparison := integral_rpow_le_one_add_integral_pow
    (finiteWeightPMF weight nonnegative normalized).toMeasure (measurable_of_finite value)
    valueNonnegative exponentNonnegative exponentBound Integrable.of_finite
  rwa [finiteWeight_integral, finiteWeight_integral] at comparison

theorem finite_inverse_moment_le_of_thinning_tail_bound
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (weight value : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (positive : ∀ outcome, 0 < value outcome) {critical start base cutoff : ℝ} (power : ℕ)
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff)
    (tailBound : ∀ depth : ℕ,
      (∑ outcome, weight outcome * (if value outcome ≤ cutoff / base ^ depth then 1 else 0)) ≤
        (thinningMap network critical)^[depth] start) :
    (∑ outcome, weight outcome * (value outcome)⁻¹ ^ power) ≤
      cutoff⁻¹ ^ power * (1 + base ^ power *
        ∑' depth : ℕ, (base ^ power) ^ depth * (thinningMap network critical)^[depth] start) := by
  have comparison := integral_inv_pow_le_of_thinning_tail_bound network
    (finiteWeightPMF weight nonnegative normalized).toMeasure power
    (measurable_of_finite value) positive criticalPositive criticalBelowOne fixedPoint scale
    startNonnegative startBelowOne baseAboveOne cutoffPositive
    (fun depth => by rw [finiteWeight_event]; exact tailBound depth)
  rwa [finiteWeight_integral] at comparison

end
end IGSIII.Chemical.SmallBall
