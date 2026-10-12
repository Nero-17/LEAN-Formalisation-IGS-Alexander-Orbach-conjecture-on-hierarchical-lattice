import IGSIII34.Diffusion.CountableProcessJointMeasurabilityCompletion
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

local instance compactOpenSampleMeasurableCompletion : MeasurableSpace C(ℝ≥0, Space) := borel _
local instance compactOpenSampleBorelCompletion : BorelSpace C(ℝ≥0, Space) := ⟨rfl⟩

def countableCompactOpenContinuousSampleCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (sample : ℕ → Space) : C(ℝ≥0, Space) :=
  ⟨countableTimeContinuousSampleCompletion times dense sample,
    countableTimeContinuousSample_continuous_completion times dense sample⟩

/-- The repaired sample operator is measurable for the genuine compact-open
Borel sigma algebra on continuous paths, not only the product sigma algebra. -/
theorem countableCompactOpenContinuousSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableCompactOpenContinuousSampleCompletion (Space := Space) times dense) := by
  let observation : C(ℝ≥0, Space) → ℕ → Space := fun path coordinate => path (times coordinate)
  have continuous : Continuous observation := continuous_pi fun coordinate => continuous_eval_const _
  have injective : Function.Injective observation := by
    intro first last equal
    apply ContinuousMap.coe_injective
    apply dense.equalizer first.continuous last.continuous
    funext coordinate
    exact congrFun equal coordinate
  have embedding := continuous.measurable.measurableEmbedding injective
  apply embedding.measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro coordinate
  exact countableTimeContinuousSample_evaluation_measurable_completion times dense (times coordinate)

def countableCompactOpenProcessProbabilityLawCompletion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (law : ProbabilityMeasure (ℕ → Space)) :
    ProbabilityMeasure C(ℝ≥0, Space) :=
  law.map (countableCompactOpenContinuousSample_measurable_completion times dense).aemeasurable

theorem countableCompactOpenProcess_observed_finite_marginal_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (law : ProbabilityMeasure (ℕ → Space))
    (regular : ∀ᵐ sample ∂(law : Measure (ℕ → Space)), countableTimeLocalUniformContinuityCompletion times sample)
    {count : ℕ} (coordinates : Fin count → ℕ) :
    (countableCompactOpenProcessProbabilityLawCompletion times dense law : Measure C(ℝ≥0, Space)).map
      (fun path => fun index : Fin count => path (times (coordinates index))) =
        (law : Measure (ℕ → Space)).map (fun sample => fun index : Fin count => sample (coordinates index)) := by
  change ((law : Measure (ℕ → Space)).map (countableCompactOpenContinuousSampleCompletion times dense)).map _ = _
  rw [Measure.map_map (by
    exact (continuous_pi fun index => continuous_eval_const _).measurable)
    (countableCompactOpenContinuousSample_measurable_completion times dense)]
  apply Measure.map_congr
  filter_upwards [countableTimeContinuousSample_ae_agreement_completion times dense law regular] with sample agree
  funext index
  exact agree (coordinates index)

end
end IGSIII34.Diffusion
