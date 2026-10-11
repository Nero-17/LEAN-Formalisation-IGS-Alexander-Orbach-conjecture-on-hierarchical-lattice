import IGSIII34.Diffusion.RoundedStoppingMarkovCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Omega Space : Type*} [MeasurableSpace Omega]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem boundedStopping_feller_condExp_completion20261011
    (measure : Measure Omega) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (process : ℝ≥0 → Omega → Space) (joint : Measurable (fun pair : ℝ≥0 × Omega => process pair.1 pair.2))
    (adapted : StronglyAdapted filtration process)
    (continuousPaths : ∀ sample, Continuous (fun present => process present sample))
    (time : Omega → ℝ≥0) (stopping : IsStoppingTime filtration (fun sample => (time sample : WithTop ℝ≥0)))
    (horizon : ℝ≥0) (bounded : ∀ sample, time sample ≤ horizon)
    (future : ℝ≥0) (test transformed : C(Space, ℝ))
    (deterministicMarkov : ∀ present : ℝ≥0,
      measure[(fun sample => test (process (present + future) sample)) | filtration present] =ᵐ[measure]
        fun sample => transformed (process present sample)) :
    measure[(fun sample => test (process (time sample + future) sample)) | stopping.measurableSpace] =ᵐ[measure]
      fun sample => transformed (process (time sample) sample) := by
  have timeMeasurable := stoppingTime_nnreal_measurable_completion20261011 filtration time stopping
  have futureIntegrable := continuousProcessTest_integrable_completion20261011 measure process joint
    (fun sample => time sample + future) (timeMeasurable.add_const future) test
  have currentIntegrable := continuousProcessTest_integrable_completion20261011 measure process joint time timeMeasurable transformed
  have stoppedMeasurable : Measurable[stopping.measurableSpace] (fun sample => process (time sample) sample) := by
    change Measurable[stopping.measurableSpace] (stoppedValue process (fun sample => (time sample : WithTop ℝ≥0)))
    exact measurable_stoppedValue (adapted.isStronglyProgressive_of_continuous continuousPaths) stopping
  have transformedStrong : StronglyMeasurable[stopping.measurableSpace]
      (fun sample => transformed (process (time sample) sample)) :=
    (transformed.continuous.measurable.comp stoppedMeasurable).stronglyMeasurable
  apply (ae_eq_condExp_of_forall_setIntegral_eq stopping.measurableSpace_le futureIntegrable
    (fun event known finite => currentIntegrable.integrableOn) ?_ transformedStrong.aestronglyMeasurable).symm
  intro event known finite
  apply Eq.symm
  apply boundedStopping_markov_setIntegral_completion20261011 measure filtration process joint continuousPaths time stopping horizon bounded
    future test transformed ?_ event known
  intro present past pastKnown
  have integrable := continuousProcessTest_integrable_completion20261011 measure process joint
    (fun _ => present + future) measurable_const test
  calc
    (∫ sample in past, test (process (present + future) sample) ∂measure) =
        ∫ sample in past, (measure[(fun sample => test (process (present + future) sample)) | filtration present]) sample ∂measure :=
      (setIntegral_condExp (filtration.le present) integrable pastKnown).symm
    _ = ∫ sample in past, transformed (process present sample) ∂measure :=
      setIntegral_congr_ae (filtration.le present _ pastKnown)
        ((deterministicMarkov present).mono fun sample equality _ => equality)

end
end IGSIII34.Diffusion
