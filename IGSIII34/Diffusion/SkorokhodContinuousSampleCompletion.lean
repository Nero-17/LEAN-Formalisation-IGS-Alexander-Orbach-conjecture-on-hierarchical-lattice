import IGSIII34.Diffusion.SkorokhodFiniteGridCompletion
import IGSIII34.Diffusion.CountablePathMeasurableExtensionCompletion
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

/-- The compact-open Borel structure on continuous interval paths is
obtained from a countable dense set of evaluations by Lusin--Souslin. -/
theorem continuousIntervalFamily_measurable_of_evaluations_completion
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sample : Outcome → C(SkorokhodIntervalTimeCompletion, Space))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
    Measurable sample := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion, Space) := ⟨rfl⟩
  letI : Nonempty SkorokhodIntervalTimeCompletion := ⟨⟨0, by norm_num⟩⟩
  let times := TopologicalSpace.denseSeq SkorokhodIntervalTimeCompletion
  have dense := TopologicalSpace.denseRange_denseSeq SkorokhodIntervalTimeCompletion
  let observation : C(SkorokhodIntervalTimeCompletion, Space) → ℕ → Space := fun path index => path (times index)
  have observationContinuous : Continuous observation := continuous_pi (fun index => continuous_eval_const (times index))
  have observationInjective : Function.Injective observation := by
    intro first second equal
    apply DFunLike.coe_injective
    apply dense.equalizer first.continuous second.continuous
    funext index
    exact congrFun equal index
  apply (observationContinuous.measurableEmbedding observationInjective).measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun index => evaluations (times index))

def countableContinuousIntervalSampleCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (sample : ℕ → Space) : C(SkorokhodIntervalTimeCompletion, Space) where
  toFun time := countableTimeContinuousSampleCompletion times dense sample ⟨time.val, time.property.1⟩
  continuous_toFun := (countableTimeContinuousSample_continuous_completion times dense sample).comp (by fun_prop)

theorem countableContinuousIntervalSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
    Measurable (countableContinuousIntervalSampleCompletion (Space := Space) times dense) := by
  apply continuousIntervalFamily_measurable_of_evaluations_completion
  intro time
  exact countableTimeContinuousSample_evaluation_measurable_completion times dense ⟨time.val, time.property.1⟩

def countableSkorokhodIntervalSampleCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (sample : ℕ → Space) : SkorokhodIntervalPathCompletion Space :=
  continuousIntervalPathCompletion (countableContinuousIntervalSampleCompletion times dense sample)

theorem countableSkorokhodIntervalSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableSkorokhodIntervalSampleCompletion (Space := Space) times dense) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion, Space) := ⟨rfl⟩
  exact continuousIntervalPath_lipschitz_completion.continuous.measurable.comp
    (countableContinuousIntervalSample_measurable_completion times dense)

end
end IGSIII34.Diffusion
