import IGSIII34.Spectral.ContinuousHistoryL2DensityCompletion
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! A paired identity against every continuous past test gives a genuine
conditional-distribution moment. The extension from continuous tests to
all measurable past information uses proved compact-history L2 density. -/
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {Outcome History Space : Type*} [MeasurableSpace Outcome]
  [MetricSpace History] [CompactSpace History] [MeasurableSpace History] [BorelSpace History]
  [TopologicalSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
  [StandardBorelSpace Space] [Nonempty Space]

theorem conditional_moment_of_continuous_past_tests_completion
    (law : Measure Outcome) [IsFiniteMeasure law]
    (history : Outcome → History) (historyMeasurable : Measurable history)
    (future : Outcome → Space) (futureMeasurable : AEMeasurable future law)
    [(law.map history).WeaklyRegular]
    (function : C(Space, ℝ)) (expectation : History → ℝ)
    (expectationMeasurable : Measurable expectation)
    (bound : ℝ) (expectationBounded : ∀ᵐ retained ∂law.map history, ‖expectation retained‖ ≤ bound)
    (paired : ∀ test : C(History, ℝ),
      (∫ outcome, test (history outcome) * function (future outcome) ∂law) =
        ∫ outcome, test (history outcome) * expectation (history outcome) ∂law) :
    (fun retained => ∫ other, function other ∂condDistrib future history law retained) =ᵐ[law.map history]
      expectation := by
  have momentMeasurable : Measurable (fun retained => ∫ other, function other ∂condDistrib future history law retained) :=
    (function.continuous.stronglyMeasurable.integral_kernel (κ := condDistrib future history law)).measurable
  have momentBounded : ∀ retained,
      ‖∫ other, function other ∂condDistrib future history law retained‖ ≤ ‖function‖ := by
    intro retained
    have boundIntegral := norm_integral_le_of_norm_le_const (μ := condDistrib future history law retained)
      (Eventually.of_forall (fun other => ContinuousMap.norm_coe_le_norm function other))
    simpa only [measureReal_univ_eq_one, mul_one] using boundIntegral
  have residualBounded : ∀ᵐ retained ∂law.map history,
      ‖(∫ other, function other ∂condDistrib future history law retained) - expectation retained‖ ≤ ‖function‖ + bound := by
    filter_upwards [expectationBounded] with retained expectationBound
    exact (norm_sub_le _ _).trans (add_le_add (momentBounded retained) expectationBound)
  have residualZero := bounded_measurable_eq_zero_of_continuous_tests_completion (law.map history)
    (fun retained => (∫ other, function other ∂condDistrib future history law retained) - expectation retained)
    ((momentMeasurable.sub expectationMeasurable).aestronglyMeasurable) (‖function‖ + bound) residualBounded
  suffices zeros : (fun retained => (∫ other, function other ∂condDistrib future history law retained) - expectation retained) =ᵐ[law.map history] 0 by
    filter_upwards [zeros] with retained zero
    exact sub_eq_zero.mp zero
  apply residualZero
  intro test
  have firstIntegrable : Integrable
      (fun retained => (∫ other, function other ∂condDistrib future history law retained) * test retained)
      (law.map history) :=
    Integrable.of_bound (momentMeasurable.mul test.continuous.measurable).aestronglyMeasurable
      (‖function‖ * ‖test‖) (Eventually.of_forall (fun retained => by
        rw [norm_mul]
        exact mul_le_mul (momentBounded retained) (ContinuousMap.norm_coe_le_norm test retained)
          (norm_nonneg _) (norm_nonneg _)))
  have secondIntegrable : Integrable (fun retained => expectation retained * test retained) (law.map history) := by
    apply Integrable.of_bound (expectationMeasurable.mul test.continuous.measurable).aestronglyMeasurable
      (bound * ‖test‖)
    filter_upwards [expectationBounded] with retained expectationBound
    change ‖expectation retained * test retained‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul expectationBound (ContinuousMap.norm_coe_le_norm test retained)
      (norm_nonneg _) (le_trans (norm_nonneg _) expectationBound)
  have jointIntegrable : Integrable (fun pair : History × Space => test pair.1 * function pair.2)
      ((law.map history) ⊗ₘ condDistrib future history law) := by
    apply Integrable.of_bound
      ((test.continuous.measurable.comp measurable_fst).mul
        (function.continuous.measurable.comp measurable_snd)).aestronglyMeasurable (‖test‖ * ‖function‖)
    apply Eventually.of_forall
    intro pair
    change ‖test pair.1 * function pair.2‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (ContinuousMap.norm_coe_le_norm test pair.1) (ContinuousMap.norm_coe_le_norm function pair.2)
      (norm_nonneg _) (norm_nonneg _)
  have firstPaired : (∫ retained, (∫ other, function other ∂condDistrib future history law retained) * test retained ∂law.map history) =
      ∫ outcome, test (history outcome) * function (future outcome) ∂law := by
    calc
      _ = ∫ retained, test retained * (∫ other, function other ∂condDistrib future history law retained) ∂law.map history := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => mul_comm _ _)
      _ = ∫ pair : History × Space, test pair.1 * function pair.2 ∂((law.map history) ⊗ₘ condDistrib future history law) := by
        rw [Measure.integral_compProd jointIntegrable]
        simp_rw [integral_const_mul]
      _ = _ := by
        rw [compProd_map_condDistrib futureMeasurable]
        exact integral_map (historyMeasurable.aemeasurable.prodMk futureMeasurable)
          (((test.continuous.measurable.comp measurable_fst).mul
            (function.continuous.measurable.comp measurable_snd)).aestronglyMeasurable)
  have secondPaired : (∫ retained, expectation retained * test retained ∂law.map history) =
      ∫ outcome, test (history outcome) * expectation (history outcome) ∂law := by
    have mapped := integral_map (μ := law) (f := fun retained => expectation retained * test retained)
      historyMeasurable.aemeasurable ((expectationMeasurable.mul test.continuous.measurable).aestronglyMeasurable)
    rw [mapped]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => mul_comm _ _)
  have expand : (fun retained => ((∫ other, function other ∂condDistrib future history law retained) - expectation retained) * test retained) =
      fun retained => (∫ other, function other ∂condDistrib future history law retained) * test retained - expectation retained * test retained := by
    funext retained
    ring
  rw [expand, integral_sub firstIntegrable secondIntegrable, firstPaired, secondPaired, paired test, sub_self]

end
end IGSIII34.Spectral
