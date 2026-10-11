import IGSIII34.Diffusion.StoppingCeilingApproximationCompletion20261011
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal BigOperators
variable {Omega Space : Type*} [MeasurableSpace Omega]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem continuousProcessTest_integrable_completion20261011
    (measure : Measure Omega) [IsFiniteMeasure measure]
    (process : ℝ≥0 → Omega → Space) (joint : Measurable (fun pair : ℝ≥0 × Omega => process pair.1 pair.2))
    (time : Omega → ℝ≥0) (timeMeasurable : Measurable time) (test : C(Space, ℝ)) :
    Integrable (fun sample => test (process (time sample) sample)) measure := by
  apply Integrable.of_bound
    (test.continuous.measurable.comp (joint.comp (timeMeasurable.prodMk measurable_id))).aestronglyMeasurable ‖test‖
  exact ae_of_all _ fun sample => test.norm_coe_le_norm _

theorem roundedStopping_markov_setIntegral_completion20261011
    (measure : Measure Omega) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (process : ℝ≥0 → Omega → Space) (joint : Measurable (fun pair : ℝ≥0 × Omega => process pair.1 pair.2))
    (time : Omega → ℝ≥0) (stopping : IsStoppingTime filtration (fun sample => (time sample : WithTop ℝ≥0)))
    (horizon : ℝ≥0) (bounded : ∀ sample, time sample ≤ horizon)
    (future : ℝ≥0) (test transformed : C(Space, ℝ))
    (markov : ∀ present : ℝ≥0, ∀ event : Set Omega, MeasurableSet[filtration present] event →
      (∫ sample in event, test (process (present + future) sample) ∂measure) =
        ∫ sample in event, transformed (process present sample) ∂measure)
    (event : Set Omega) (eventKnown : MeasurableSet[stopping.measurableSpace] event) (index : ℕ) :
    (∫ sample in event, test (process (stoppingCeilingTimeCompletion20261011 index (time sample) + future) sample) ∂measure) =
      ∫ sample in event, transformed (process (stoppingCeilingTimeCompletion20261011 index (time sample)) sample) ∂measure := by
  classical
  let limit := ⌈((index + 1 : ℕ) : ℝ≥0) * horizon⌉₊
  let cell : ℕ → Set Omega := fun number => event ∩ {sample | ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ = number}
  have cellKnown (number : ℕ) : MeasurableSet[filtration ((number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0))] (cell number) :=
    stoppingCeilingCell_measurable_completion20261011 filtration time stopping event eventKnown index number
  have cellMeasurable (number : ℕ) : MeasurableSet (cell number) :=
    filtration.le _ _ (cellKnown number)
  have ceilingBound (sample : Omega) : ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊ ≤ limit :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left (bounded sample) zero_le)
  have expansion (function : C(Space, ℝ)) (offset : ℝ≥0) :
      event.indicator (fun sample => function (process (stoppingCeilingTimeCompletion20261011 index (time sample) + offset) sample)) =
        fun sample => ∑ number ∈ Finset.range (limit + 1),
          (cell number).indicator (fun sample => function (process ((number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) + offset) sample)) sample := by
    funext sample
    by_cases member : sample ∈ event
    · let selected := ⌈((index + 1 : ℕ) : ℝ≥0) * time sample⌉₊
      rw [Finset.sum_eq_single selected]
      · simp [cell, member, selected, stoppingCeilingTimeCompletion20261011]
      · intro number inRange different
        have outside : sample ∉ cell number := by
          simp only [cell, mem_inter_iff, mem_setOf_eq, member, true_and]
          exact Ne.symm different
        exact Set.indicator_of_notMem outside _
      · intro outside
        exact False.elim (outside (Finset.mem_range.mpr (Nat.lt_succ_of_le (ceilingBound sample))))
    · simp [cell, member]
  have integrableCell (function : C(Space, ℝ)) (offset : ℝ≥0) (number : ℕ) :
      Integrable ((cell number).indicator (fun sample => function (process ((number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) + offset) sample))) measure :=
    (continuousProcessTest_integrable_completion20261011 measure process joint
      (fun _ => (number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0) + offset) measurable_const function).indicator (cellMeasurable number)
  rw [← integral_indicator eventKnown.1, ← integral_indicator eventKnown.1]
  have transformedExpansion := expansion transformed 0
  simp only [add_zero] at transformedExpansion
  rw [expansion test future, transformedExpansion,
    integral_finsetSum _ (fun number _ => integrableCell test future number),
    integral_finsetSum _ (fun number _ => by simpa only [add_zero] using integrableCell transformed 0 number)]
  apply Finset.sum_congr rfl
  intro number inRange
  rw [integral_indicator (cellMeasurable number), integral_indicator (cellMeasurable number)]
  simpa only [add_zero] using markov ((number : ℝ≥0) / ((index + 1 : ℕ) : ℝ≥0)) (cell number) (cellKnown number)

theorem boundedStopping_markov_setIntegral_completion20261011
    (measure : Measure Omega) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (process : ℝ≥0 → Omega → Space) (joint : Measurable (fun pair : ℝ≥0 × Omega => process pair.1 pair.2))
    (continuousPaths : ∀ sample, Continuous (fun present => process present sample))
    (time : Omega → ℝ≥0) (stopping : IsStoppingTime filtration (fun sample => (time sample : WithTop ℝ≥0)))
    (horizon : ℝ≥0) (bounded : ∀ sample, time sample ≤ horizon)
    (future : ℝ≥0) (test transformed : C(Space, ℝ))
    (markov : ∀ present : ℝ≥0, ∀ event : Set Omega, MeasurableSet[filtration present] event →
      (∫ sample in event, test (process (present + future) sample) ∂measure) =
        ∫ sample in event, transformed (process present sample) ∂measure)
    (event : Set Omega) (eventKnown : MeasurableSet[stopping.measurableSpace] event) :
    (∫ sample in event, test (process (time sample + future) sample) ∂measure) =
      ∫ sample in event, transformed (process (time sample) sample) ∂measure := by
  have timeMeasurable := stoppingTime_nnreal_measurable_completion20261011 filtration time stopping
  have testLimit : Tendsto (fun index => ∫ sample in event,
      test (process (stoppingCeilingTimeCompletion20261011 index (time sample) + future) sample) ∂measure) atTop
      (𝓝 (∫ sample in event, test (process (time sample + future) sample) ∂measure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
    · intro index
      exact (test.continuous.measurable.comp (joint.comp
        (((stoppingCeilingTime_measurable_completion20261011 time timeMeasurable index).add_const future).prodMk measurable_id))).aestronglyMeasurable
    · exact integrable_const _
    · intro index
      exact ae_of_all _ fun sample => test.norm_coe_le_norm _
    · exact ae_of_all _ fun sample => test.continuous.continuousAt.tendsto.comp
        ((continuousPaths sample).continuousAt.tendsto.comp
          ((stoppingCeilingTime_tendsto_completion20261011 (time sample)).add_const future))
  have transformedLimit : Tendsto (fun index => ∫ sample in event,
      transformed (process (stoppingCeilingTimeCompletion20261011 index (time sample)) sample) ∂measure) atTop
      (𝓝 (∫ sample in event, transformed (process (time sample) sample) ∂measure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖transformed‖)
    · intro index
      exact (transformed.continuous.measurable.comp (joint.comp
        ((stoppingCeilingTime_measurable_completion20261011 time timeMeasurable index).prodMk measurable_id))).aestronglyMeasurable
    · exact integrable_const _
    · intro index
      exact ae_of_all _ fun sample => transformed.norm_coe_le_norm _
    · exact ae_of_all _ fun sample => transformed.continuous.continuousAt.tendsto.comp
        ((continuousPaths sample).continuousAt.tendsto.comp (stoppingCeilingTime_tendsto_completion20261011 (time sample)))
  have integralIdentity : (fun index => ∫ sample in event,
      test (process (stoppingCeilingTimeCompletion20261011 index (time sample) + future) sample) ∂measure) =
      (fun index => ∫ sample in event, transformed (process (stoppingCeilingTimeCompletion20261011 index (time sample)) sample) ∂measure) := by
    funext index
    exact roundedStopping_markov_setIntegral_completion20261011 measure filtration process joint time stopping horizon bounded
      future test transformed markov event eventKnown index
  rw [integralIdentity] at testLimit
  exact tendsto_nhds_unique testLimit transformedLimit

end
end IGSIII34.Diffusion
