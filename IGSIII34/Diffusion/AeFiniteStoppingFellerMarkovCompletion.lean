import IGSIII34.Diffusion.WithTopBoundedEventMarkovCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Omega Space : Type*} [MeasurableSpace Omega]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem aeFiniteStopping_markov_setIntegral_completion
    (measure : Measure Omega) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (process : ℝ≥0 → Omega → Space) (joint : Measurable (fun pair : ℝ≥0 × Omega => process pair.1 pair.2))
    (continuousPaths : ∀ sample, Continuous (fun present => process present sample))
    (time : Omega → WithTop ℝ≥0) (stopping : IsStoppingTime filtration time)
    (finiteTime : ∀ᵐ sample ∂measure, time sample ≠ ⊤)
    (future : ℝ≥0) (test transformed : C(Space, ℝ))
    (markov : ∀ present : ℝ≥0, ∀ event : Set Omega, MeasurableSet[filtration present] event →
      (∫ sample in event, test (process (present + future) sample) ∂measure) =
        ∫ sample in event, transformed (process present sample) ∂measure)
    (event : Set Omega) (eventKnown : MeasurableSet[stopping.measurableSpace] event) :
    (∫ sample in event, test (process ((time sample).untopA + future) sample) ∂measure) =
      ∫ sample in event, transformed (process ((time sample).untopA) sample) ∂measure := by
  let events : ℕ → Set Omega := fun index => event ∩ {sample | time sample ≤ (index : ℝ≥0)}
  have known (index : ℕ) : MeasurableSet[stopping.measurableSpace] (events index) :=
    eventKnown.inter (stopping.measurableSet_le' (index : ℝ≥0))
  have eventMeasurable (index : ℕ) : MeasurableSet (events index) := stopping.measurableSpace_le _ (known index)
  have timeMeasurable := stopping.measurable'.untopA
  have integralLimit (function : C(Space, ℝ)) (offset : ℝ≥0) :
      Tendsto (fun index => ∫ sample, (events index).indicator
        (fun sample => function (process ((time sample).untopA + offset) sample)) sample ∂measure) atTop
        (𝓝 (∫ sample, event.indicator (fun sample => function (process ((time sample).untopA + offset) sample)) sample ∂measure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖function‖)
    · intro index
      exact ((function.continuous.measurable.comp (joint.comp
        ((timeMeasurable.add_const offset).prodMk measurable_id))).indicator (eventMeasurable index)).aestronglyMeasurable
    · exact integrable_const _
    · intro index
      apply ae_of_all
      intro sample
      by_cases member : sample ∈ events index
      · rw [Set.indicator_of_mem member]
        exact function.norm_coe_le_norm _
      · rw [Set.indicator_of_notMem member, norm_zero]
        exact norm_nonneg _
    · filter_upwards [finiteTime] with sample isFinite
      have eventuallyAbove : ∀ᶠ index : ℕ in atTop, (time sample).untopA ≤ (index : ℝ≥0) :=
        (tendsto_natCast_atTop_atTop : Tendsto (fun index : ℕ => (index : ℝ≥0)) atTop atTop).eventually_ge_atTop ((time sample).untopA)
      have stable : ∀ᶠ index in atTop, (events index).indicator (fun sample => function (process ((time sample).untopA + offset) sample)) sample =
          event.indicator (fun sample => function (process ((time sample).untopA + offset) sample)) sample := by
        filter_upwards [eventuallyAbove] with index above
        have lifted : time sample ≤ (index : ℝ≥0) := (WithTop.untopA_le_iff isFinite).mp above
        by_cases member : sample ∈ event
        · rw [Set.indicator_of_mem (show sample ∈ events index from ⟨member, lifted⟩), Set.indicator_of_mem member]
        · simp [events, member]
      exact tendsto_const_nhds.congr' (stable.mono fun index equality => equality.symm)
  have identity (index : ℕ) :
      (∫ sample, (events index).indicator (fun sample => test (process ((time sample).untopA + future) sample)) sample ∂measure) =
        ∫ sample, (events index).indicator (fun sample => transformed (process ((time sample).untopA) sample)) sample ∂measure := by
    rw [integral_indicator (eventMeasurable index), integral_indicator (eventMeasurable index)]
    apply withTopStopping_markov_on_bounded_event_setIntegral_completion measure filtration process joint continuousPaths
      time stopping (events index) (known index) (index : ℝ≥0) ?_ future test transformed markov
    intro sample member
    exact member.2
  have futureLimit := integralLimit test future
  have currentLimit := integralLimit transformed 0
  simp only [add_zero] at currentLimit
  have equality : (fun index => ∫ sample, (events index).indicator (fun sample => test (process ((time sample).untopA + future) sample)) sample ∂measure) =
      (fun index => ∫ sample, (events index).indicator (fun sample => transformed (process ((time sample).untopA) sample)) sample ∂measure) := funext identity
  rw [equality] at futureLimit
  have finalEquality := tendsto_nhds_unique futureLimit currentLimit
  simpa only [integral_indicator eventKnown.1] using finalEquality

theorem aeFiniteStopping_feller_condExp_completion
    (measure : Measure Omega) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (process : ℝ≥0 → Omega → Space) (joint : Measurable (fun pair : ℝ≥0 × Omega => process pair.1 pair.2))
    (adapted : StronglyAdapted filtration process)
    (continuousPaths : ∀ sample, Continuous (fun present => process present sample))
    (time : Omega → WithTop ℝ≥0) (stopping : IsStoppingTime filtration time)
    (finiteTime : ∀ᵐ sample ∂measure, time sample ≠ ⊤)
    (future : ℝ≥0) (test transformed : C(Space, ℝ))
    (deterministicMarkov : ∀ present : ℝ≥0,
      measure[(fun sample => test (process (present + future) sample)) | filtration present] =ᵐ[measure]
        fun sample => transformed (process present sample)) :
    measure[(fun sample => test (process ((time sample).untopA + future) sample)) | stopping.measurableSpace] =ᵐ[measure]
      fun sample => transformed (process ((time sample).untopA) sample) := by
  have timeMeasurable := stopping.measurable'.untopA
  have futureIntegrable := continuousProcessTest_integrable_completion measure process joint
    (fun sample => (time sample).untopA + future) (timeMeasurable.add_const future) test
  have currentIntegrable := continuousProcessTest_integrable_completion measure process joint (fun sample => (time sample).untopA) timeMeasurable transformed
  have stoppedMeasurable : Measurable[stopping.measurableSpace] (fun sample => process ((time sample).untopA) sample) := by
    change Measurable[stopping.measurableSpace] (stoppedValue process time)
    exact measurable_stoppedValue (adapted.isStronglyProgressive_of_continuous continuousPaths) stopping
  have transformedStrong : StronglyMeasurable[stopping.measurableSpace]
      (fun sample => transformed (process ((time sample).untopA) sample)) :=
    (transformed.continuous.measurable.comp stoppedMeasurable).stronglyMeasurable
  apply (ae_eq_condExp_of_forall_setIntegral_eq stopping.measurableSpace_le futureIntegrable
    (fun event known finite => currentIntegrable.integrableOn) ?_ transformedStrong.aestronglyMeasurable).symm
  intro event known finite
  apply Eq.symm
  apply aeFiniteStopping_markov_setIntegral_completion measure filtration process joint continuousPaths time stopping finiteTime
    future test transformed ?_ event known
  intro present past pastKnown
  have integrable := continuousProcessTest_integrable_completion measure process joint
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


