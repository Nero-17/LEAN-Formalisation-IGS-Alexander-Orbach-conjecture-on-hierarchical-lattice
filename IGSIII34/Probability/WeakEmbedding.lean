import IGSIII34.Topology.Schauder
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false

namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction _root_.Topology

variable {Outcome : Type*} [TopologicalSpace Outcome] [MeasurableSpace Outcome]
  [BorelSpace Outcome] [HasOuterApproxClosed Outcome]

def integralEmbedding (law : ProbabilityMeasure Outcome) : (Outcome →ᵇ ℝ) → ℝ :=
  fun test => ∫ outcome, test outcome ∂(law : Measure Outcome)

theorem integralEmbedding_continuous : Continuous (integralEmbedding (Outcome := Outcome)) := by
  apply continuous_pi
  intro test
  apply continuous_iff_continuousAt.mpr
  intro law
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (continuous_id.continuousAt (x := law))) test

theorem integralEmbedding_injective : Function.Injective (integralEmbedding (Outcome := Outcome)) := by
  intro first second equality
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding Outcome).injective
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro test
  exact congrFun equality test

theorem integralEmbedding_isEmbedding :
    IsEmbedding (integralEmbedding (Outcome := Outcome)) := by
  refine ⟨isInducing_iff_nhds.mpr ?_, integralEmbedding_injective⟩
  intro law
  apply le_antisymm
  · exact Filter.map_le_iff_le_comap.mp (integralEmbedding_continuous.continuousAt (x := law))
  · change Tendsto id (Filter.comap integralEmbedding (𝓝 (integralEmbedding law))) (𝓝 law)
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro test
    exact (tendsto_pi_nhds.mp (show Tendsto integralEmbedding
      (Filter.comap integralEmbedding (𝓝 (integralEmbedding law))) (𝓝 (integralEmbedding law))
      from tendsto_comap)) test

end
end IGSIII34.Probability
