import IGSIII34.Diffusion.CountableContinuousProcessCompletion
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory
open scoped NNReal

theorem countableTimeContinuousSample_joint_measurable_completion
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (fun pair : ℝ≥0 × (ℕ → Space) =>
      countableTimeContinuousSampleCompletion times dense pair.2 pair.1) :=
  measurable_uncurry_of_continuous_of_measurable
    (countableTimeContinuousSample_continuous_completion times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion times dense)

end
end IGSIII34.Diffusion
