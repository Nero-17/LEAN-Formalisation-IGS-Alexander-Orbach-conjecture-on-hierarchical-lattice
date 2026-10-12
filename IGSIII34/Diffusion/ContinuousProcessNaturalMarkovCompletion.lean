import IGSIII34.Diffusion.CountableHistoryConditionalExpectationCompletion
import IGSIII34.Diffusion.NaturalDensePastCompletion

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped _root_.Topology NNReal ProbabilityTheory
variable {Outcome Space : Type*} [MeasurableSpace Outcome]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space] [Nonempty Space]

/-- Genuine finite-history transition kernels imply the Markov identity
for the entire natural past of a continuous process. Lévy's upward
theorem supplies the countable-past passage, and path continuity supplies
the equality with the full real-time natural filtration. -/
theorem continuous_process_natural_markov_of_finite_histories_completion
    (law : Measure Outcome) [IsFiniteMeasure law]
    (sample : Outcome → ℝ≥0 → Space) (sampleContinuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (present future : ℝ≥0)
    (transition : Kernel Space Space) [IsMarkovKernel transition]
    (finite : ∀ count,
      condDistrib (fun outcome => sample outcome future)
        (fun outcome => fun coordinate : Fin (count+1) => sample outcome
          (countableDensePastTimeCompletion times present coordinate.val)) law =ᵐ[law.map
            (fun outcome => fun coordinate : Fin (count+1) => sample outcome
              (countableDensePastTimeCompletion times present coordinate.val))]
        transition.comap (fun history : Fin (count+1) → Space => history 0) (measurable_pi_apply 0))
    (function : C(Space, ℝ)) :
    law[(fun outcome => function (sample outcome future)) |
      Filtration.natural (fun time outcome => sample outcome time) (fun time => (evaluations time).stronglyMeasurable) present] =ᵐ[law]
        (fun outcome => ∫ value, function value ∂transition (sample outcome present)) := by
  let history : ℕ → Outcome → Space := fun coordinate outcome =>
    sample outcome (countableDensePastTimeCompletion times present coordinate)
  have historyStrong (coordinate : ℕ) : StronglyMeasurable (history coordinate) := (evaluations _).stronglyMeasurable
  have boundedFunction : Integrable (fun outcome => function (sample outcome future)) law :=
    Integrable.of_bound (function.continuous.measurable.comp (evaluations future)).aestronglyMeasurable
      ‖function‖ (Eventually.of_forall (fun outcome => ContinuousMap.norm_coe_le_norm function _))
  have whole := conditional_expectation_of_all_finite_histories_completion law history historyStrong
    (fun outcome => function (sample outcome future)) (fun outcome => ∫ value, function value ∂transition (sample outcome present)) ?_
  · have sigmaIdentity := countable_dense_past_generates_natural_completion times dense sample sampleContinuous present
    change MeasurableSpace.comap (fun outcome coordinate => history coordinate outcome) inferInstance =
      Filtration.natural (fun time outcome => sample outcome time) (fun time => (evaluations time).stronglyMeasurable) present at sigmaIdentity
    rwa [sigmaIdentity] at whole
  · intro count
    let finiteHistory := fun outcome => fun coordinate : Fin (count+1) => history coordinate.val outcome
    have finiteMeasurable : Measurable finiteHistory := measurable_pi_lambda _ (fun coordinate => evaluations _)
    have conditional := condExp_ae_eq_integral_condDistrib finiteMeasurable (evaluations future).aemeasurable
      function.continuous.stronglyMeasurable boundedFunction
    have pulled := ae_of_ae_map finiteMeasurable.aemeasurable (finite count)
    apply conditional.trans
    filter_upwards [pulled] with outcome same
    rw [same]
    rfl

end
end IGSIII34.Diffusion
