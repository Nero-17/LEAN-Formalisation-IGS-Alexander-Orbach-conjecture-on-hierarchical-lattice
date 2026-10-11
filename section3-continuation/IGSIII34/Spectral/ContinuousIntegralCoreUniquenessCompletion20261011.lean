import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! A uniformly dense linear spectral core determines finite measures and
transition kernels. The integration functional is constructed as a genuine
continuous linear map through L1. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {Space Index : Type*} [TopologicalSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def continuousMapIntegralCompletion20261011 (measure : Measure Space)
    [IsFiniteMeasure measure] : C(Space, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := measure) (E := ℝ)).comp (ContinuousMap.toLp 1 measure ℝ)

theorem continuousMapIntegral_apply_completion20261011 (measure : Measure Space)
    [IsFiniteMeasure measure] (function : C(Space, ℝ)) :
    continuousMapIntegralCompletion20261011 measure function = ∫ point, function point ∂measure := by
  change L1.integralCLM (ContinuousMap.toLp 1 measure ℝ function) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) measure function)

theorem finite_measures_eq_of_dense_continuous_core_completion20261011
    [HasOuterApproxClosed Space]
    (core : Index → C(Space, ℝ))
    (coreDense : Dense ((Submodule.span ℝ (Set.range core)) : Set C(Space, ℝ)))
    (first second : Measure Space) [IsFiniteMeasure first] [IsFiniteMeasure second]
    (same : ∀ index, (∫ point, core index point ∂first) = ∫ point, core index point ∂second) :
    first = second := by
  have operators : continuousMapIntegralCompletion20261011 first =
      continuousMapIntegralCompletion20261011 second := by
    apply ContinuousLinearMap.ext_on coreDense
    rintro _ ⟨index,rfl⟩
    simpa only [continuousMapIntegral_apply_completion20261011] using same index
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro function
  have evaluation := congrArg (fun operator => operator function.toContinuousMap) operators
  simpa only [continuousMapIntegral_apply_completion20261011, BoundedContinuousFunction.coe_toContinuousMap] using evaluation

end
end IGSIII34.Spectral
