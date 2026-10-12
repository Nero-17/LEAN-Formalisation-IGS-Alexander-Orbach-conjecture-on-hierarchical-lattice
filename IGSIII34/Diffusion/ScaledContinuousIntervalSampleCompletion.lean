import IGSIII34.Diffusion.SkorokhodContinuousSampleCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def countableScaledContinuousIntervalSampleCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (horizon : ℝ≥0) (path : ℕ → Space) : C(SkorokhodIntervalTimeCompletion, Space) where
  toFun time := countableTimeContinuousSampleCompletion times dense path (horizon * ⟨time.val, time.property.1⟩)
  continuous_toFun := (countableTimeContinuousSample_continuous_completion times dense path).comp (by fun_prop)

theorem countableScaledContinuousIntervalSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (horizon : ℝ≥0) :
    letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
    Measurable (countableScaledContinuousIntervalSampleCompletion (Space := Space) times dense horizon) := by
  apply continuousIntervalFamily_measurable_of_evaluations_completion
    (Space := Space) (countableScaledContinuousIntervalSampleCompletion times dense horizon)
  intro time
  exact countableTimeContinuousSample_evaluation_measurable_completion
    (Space := Space) times dense (horizon * ⟨time.val, time.property.1⟩)

def countableScaledSkorokhodIntervalSampleCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (horizon : ℝ≥0) (path : ℕ → Space) : SkorokhodIntervalPathCompletion Space :=
  continuousIntervalPathCompletion (countableScaledContinuousIntervalSampleCompletion times dense horizon path)

theorem countableScaledSkorokhodIntervalSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (horizon : ℝ≥0) :
    Measurable (countableScaledSkorokhodIntervalSampleCompletion (Space := Space) times dense horizon) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion, Space) := ⟨rfl⟩
  exact continuousIntervalPath_lipschitz_completion.continuous.measurable.comp
    (countableScaledContinuousIntervalSample_measurable_completion times dense horizon)

end
end IGSIII34.Diffusion
