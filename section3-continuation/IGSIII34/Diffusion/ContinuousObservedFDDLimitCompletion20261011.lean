import IGSIII34.Diffusion.CompactOpenContinuousSampleCompletion20261011
import IGSIII34.Diffusion.CountableTimeLimitsCompletion20261011

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
local instance : MeasurableSpace C(ℝ≥0, Space) := borel _
local instance : BorelSpace C(ℝ≥0, Space) := ⟨rfl⟩

def continuousObservedFDDLimitCompletion20261011
    (laws : ℕ → ProbabilityMeasure (ℕ → Space)) (times : ℕ → ℝ≥0) : Prop :=
  ∃ pathLaw : ProbabilityMeasure C(ℝ≥0, Space),
    ∀ (count : ℕ) (coordinates : Fin count → ℕ),
      Tendsto (fun depth => (laws depth).map
        (show AEMeasurable (fun sample => fun index : Fin count => sample (coordinates index)) _ from
          (by fun_prop : Measurable _).aemeasurable)) atTop
        (𝓝 (pathLaw.map (show AEMeasurable
          (fun path => fun index : Fin count => path (times (coordinates index))) _ from
          (continuous_pi fun index => continuous_eval_const _).measurable.aemeasurable)))

end
end IGSIII34.Diffusion
