import IGSIII34.Spectral.ContinuousKernelMarkovCompletion
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space] [T2Space Space]
  [SecondCountableTopology Space] [MeasurableSpace Space] [BorelSpace Space]
  (measure : Measure Space) [IsProbabilityMeasure measure]

def continuousTransitionKernelCompletion (kernel : C(Space × Space, ℝ)) : Kernel Space Space :=
  (Kernel.const Space measure).withDensity (fun first second => ENNReal.ofReal (kernel (first, second)))

theorem continuousTransitionKernel_apply_completion (kernel : C(Space × Space, ℝ)) (point : Space) :
    continuousTransitionKernelCompletion measure kernel point =
    measure.withDensity (fun other => ENNReal.ofReal (kernel (point, other))) := by
  rw [continuousTransitionKernelCompletion, Kernel.withDensity_apply]
  · rfl
  · exact ENNReal.measurable_ofReal.comp kernel.continuous.measurable

theorem continuousTransitionKernel_isMarkov_completion
    (kernel : C(Space × Space, ℝ))
    (nonnegative : ∀ first second, 0 ≤ kernel (first, second))
    (rows : ∀ first, ∫ second, kernel (first, second) ∂measure = 1) :
    IsMarkovKernel (continuousTransitionKernelCompletion measure kernel) := by
  constructor
  intro point
  constructor
  rw [continuousTransitionKernel_apply_completion, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have integrable : Integrable (fun other => kernel (point, other)) measure :=
    (BoundedContinuousFunction.mkOfCompact (kernel.curry point)).integrable measure
  rw [← ofReal_integral_eq_lintegral_ofReal integrable (Eventually.of_forall (nonnegative point)), rows]
  simp

def continuousTransitionProbabilityCompletion
    (kernel : C(Space × Space, ℝ))
    (nonnegative : ∀ first second, 0 ≤ kernel (first, second))
    (rows : ∀ first, ∫ second, kernel (first, second) ∂measure = 1) (point : Space) : ProbabilityMeasure Space :=
  letI := continuousTransitionKernel_isMarkov_completion measure kernel nonnegative rows
  ⟨continuousTransitionKernelCompletion measure kernel point, inferInstance⟩

end
end IGSIII34.Spectral
