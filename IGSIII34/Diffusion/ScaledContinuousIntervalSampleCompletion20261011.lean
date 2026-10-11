import IGSIII34.Diffusion.SkorokhodContinuousSampleCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def countableScaledContinuousIntervalSampleCompletion20261011 (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (horizon : ℝ≥0) (path : ℕ → Space) : C(SkorokhodIntervalTimeCompletion20261011, Space) where
  toFun time := countableTimeContinuousSampleCompletion20261011 times dense path (horizon * ⟨time.val, time.property.1⟩)
  continuous_toFun := (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (by fun_prop)

theorem countableScaledContinuousIntervalSample_measurable_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (horizon : ℝ≥0) :
    letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := borel _
    Measurable (countableScaledContinuousIntervalSampleCompletion20261011 (Space := Space) times dense horizon) := by
  apply continuousIntervalFamily_measurable_of_evaluations_completion20261011
    (Space := Space) (countableScaledContinuousIntervalSampleCompletion20261011 times dense horizon)
  intro time
  exact countableTimeContinuousSample_evaluation_measurable_completion20261011
    (Space := Space) times dense (horizon * ⟨time.val, time.property.1⟩)

def countableScaledSkorokhodIntervalSampleCompletion20261011 (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (horizon : ℝ≥0) (path : ℕ → Space) : SkorokhodIntervalPathCompletion20261011 Space :=
  continuousIntervalPathCompletion20261011 (countableScaledContinuousIntervalSampleCompletion20261011 times dense horizon path)

theorem countableScaledSkorokhodIntervalSample_measurable_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (horizon : ℝ≥0) :
    Measurable (countableScaledSkorokhodIntervalSampleCompletion20261011 (Space := Space) times dense horizon) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := ⟨rfl⟩
  exact continuousIntervalPath_lipschitz_completion20261011.continuous.measurable.comp
    (countableScaledContinuousIntervalSample_measurable_completion20261011 times dense horizon)

end
end IGSIII34.Diffusion
