import IGSIII34.Diffusion.CountableProcessJointMeasurabilityCompletion
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal

variable {Space Samples : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [MeasurableSpace Samples]

def continuousProcessFiniteTimeLawCompletion
    (law : ProbabilityMeasure Samples) (process : Samples → ℝ≥0 → Space)
    (evaluationMeasurable : ∀ time, Measurable (fun sample => process sample time))
    {count : ℕ} (times : Fin count → ℝ≥0) : ProbabilityMeasure (Fin count → Space) :=
  law.map (show AEMeasurable (fun sample => fun index : Fin count => process sample (times index)) law from
    (measurable_pi_lambda _ fun index => evaluationMeasurable (times index)).aemeasurable)

/-- Continuous sample paths make the full finite-dimensional law jointly
weakly continuous in all real times. This is proved by bounded dominated
convergence, rather than assumed as a process regularity property. -/
theorem continuousProcessFiniteTimeLaw_continuous_completion
    (law : ProbabilityMeasure Samples) (process : Samples → ℝ≥0 → Space)
    (evaluationMeasurable : ∀ time, Measurable (fun sample => process sample time))
    (continuousPaths : ∀ᵐ sample ∂(law : Measure Samples), Continuous (process sample))
    (count : ℕ) :
    Continuous (fun times : Fin count → ℝ≥0 =>
      continuousProcessFiniteTimeLawCompletion law process evaluationMeasurable times) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro test
  have meas (times : Fin count → ℝ≥0) : Measurable
      (fun sample => test (fun index => process sample (times index))) :=
    test.continuous.measurable.comp (measurable_pi_lambda _ fun index => evaluationMeasurable (times index))
  have continuousIntegral : Continuous (fun times : Fin count → ℝ≥0 =>
      ∫ sample, test (fun index => process sample (times index)) ∂law) := by
    apply continuous_of_dominated (bound := fun _ => ‖test‖)
    · exact fun times => (meas times).aestronglyMeasurable
    · exact fun times => Eventually.of_forall fun sample => test.norm_coe_le_norm _
    · exact integrable_const _
    · filter_upwards [continuousPaths] with sample pathContinuous
      exact test.continuous.comp (continuous_pi fun index => pathContinuous.comp (continuous_apply index))
  apply continuousIntegral.congr
  intro times
  symm
  exact integral_map (measurable_pi_lambda _ fun index => evaluationMeasurable (times index)).aemeasurable
    test.continuous.aestronglyMeasurable

/-- The canonical continuous extension of a genuine observation-law limit
therefore has jointly continuous finite-dimensional laws at all real times. -/
theorem countableContinuousProcess_finiteTimeLaw_continuous_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (law : ProbabilityMeasure (ℕ → Space)) (count : ℕ) :
    Continuous (fun futureTimes : Fin count → ℝ≥0 =>
      continuousProcessFiniteTimeLawCompletion law
        (countableTimeContinuousSampleCompletion times dense)
        (fun time => (measurable_pi_apply time).comp (countableTimeContinuousSample_measurable_completion times dense)) futureTimes) := by
  exact continuousProcessFiniteTimeLaw_continuous_completion law _ _
    (Eventually.of_forall fun sample => countableTimeContinuousSample_continuous_completion times dense sample) count

end
end IGSIII34.Diffusion

