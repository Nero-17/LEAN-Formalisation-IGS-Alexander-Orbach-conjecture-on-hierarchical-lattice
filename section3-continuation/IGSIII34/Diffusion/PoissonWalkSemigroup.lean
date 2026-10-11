import IGSIII34.Diffusion.DiscreteWalkProcess
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.Composition.Comp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

instance finiteWalkKernel_pow_markov (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (count : ℕ) :
    IsMarkovKernel (finiteWalkKernel endpoint positiveDegree ^ count) := by
  induction count with
  | zero =>
    rw [pow_zero]
    change IsMarkovKernel (Kernel.id : Kernel Vertex Vertex)
    infer_instance
  | succ count induction =>
    letI := induction
    rw [pow_succ]
    change IsMarkovKernel ((finiteWalkKernel endpoint positiveDegree ^ count) ∘ₖ
      finiteWalkKernel endpoint positiveDegree)
    infer_instance

/-- A continuous-time transition kernel constructed directly by genuine
Poisson mixing of the actual finite-graph neighbour-kernel powers. -/
def poissonWalkKernel (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℝ≥0) : Kernel Vertex Vertex :=
  Kernel.ofFunOfCountable (fun first => (poissonMeasure time).bind
    (fun count : ℕ => (finiteWalkKernel endpoint positiveDegree ^ count) first))

theorem poissonWalkKernel_apply (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℝ≥0) (first : Vertex) :
    poissonWalkKernel endpoint positiveDegree time first = (poissonMeasure time).bind
      (fun count : ℕ => (finiteWalkKernel endpoint positiveDegree ^ count) first) := rfl

instance poissonWalkKernel_markov (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℝ≥0) :
    IsMarkovKernel (poissonWalkKernel endpoint positiveDegree time) := by
  constructor
  intro first
  rw [poissonWalkKernel_apply]
  exact isProbabilityMeasure_bind (m := poissonMeasure time)
    (f := fun count : ℕ => (finiteWalkKernel endpoint positiveDegree ^ count) first)
    (measurable_of_countable _).aemeasurable (Filter.Eventually.of_forall (fun count => by infer_instance))

theorem poissonWalkKernel_apply_set (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℝ≥0) (first : Vertex)
    (set : Set Vertex) (setMeasurable : MeasurableSet set) :
    poissonWalkKernel endpoint positiveDegree time first set =
      ∫⁻ count : ℕ, (finiteWalkKernel endpoint positiveDegree ^ count) first set ∂poissonMeasure time := by
  rw [poissonWalkKernel_apply, Measure.bind_apply setMeasurable (measurable_of_countable _).aemeasurable]

/-- Full continuous-time Chapman--Kolmogorov for the constructed kernels.
The proof uses the proved Poisson convolution law and discrete kernel powers. -/
theorem poissonWalkKernel_chapman_kolmogorov (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (firstTime lastTime : ℝ≥0) :
    poissonWalkKernel endpoint positiveDegree (firstTime + lastTime) =
      poissonWalkKernel endpoint positiveDegree lastTime ∘ₖ
        poissonWalkKernel endpoint positiveDegree firstTime := by
  ext first set setMeasurable
  rw [Kernel.comp_apply' _ _ _ setMeasurable]
  calc
    _ = ∫⁻ count : ℕ, (finiteWalkKernel endpoint positiveDegree ^ count) first set
        ∂poissonMeasure (firstTime + lastTime) :=
      poissonWalkKernel_apply_set endpoint positiveDegree _ first set setMeasurable
    _ = ∫⁻ firstCount : ℕ, ∫⁻ lastCount : ℕ,
        (finiteWalkKernel endpoint positiveDegree ^ (firstCount + lastCount)) first set
        ∂poissonMeasure lastTime ∂poissonMeasure firstTime := by
      rw [← poissonMeasure_conv_poissonMeasure firstTime lastTime,
        Measure.lintegral_conv (measurable_of_countable _)]
    _ = ∫⁻ firstCount : ℕ, ∫⁻ lastCount : ℕ, ∫⁻ middle : Vertex,
        (finiteWalkKernel endpoint positiveDegree ^ lastCount) middle set
        ∂(finiteWalkKernel endpoint positiveDegree ^ firstCount) first
        ∂poissonMeasure lastTime ∂poissonMeasure firstTime := by
      apply lintegral_congr
      intro firstCount
      apply lintegral_congr
      intro lastCount
      exact Kernel.pow_add_apply_eq_lintegral _ firstCount lastCount first setMeasurable
    _ = ∫⁻ firstCount : ℕ, ∫⁻ middle : Vertex, ∫⁻ lastCount : ℕ,
        (finiteWalkKernel endpoint positiveDegree ^ lastCount) middle set
        ∂poissonMeasure lastTime ∂(finiteWalkKernel endpoint positiveDegree ^ firstCount) first
        ∂poissonMeasure firstTime := by
      apply lintegral_congr
      intro firstCount
      exact lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
    _ = ∫⁻ middle : Vertex, ∫⁻ lastCount : ℕ,
        (finiteWalkKernel endpoint positiveDegree ^ lastCount) middle set
        ∂poissonMeasure lastTime ∂poissonWalkKernel endpoint positiveDegree firstTime first := by
      rw [poissonWalkKernel_apply, lintegral_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
    _ = _ := by
      apply lintegral_congr
      intro middle
      exact (poissonWalkKernel_apply_set endpoint positiveDegree lastTime middle set setMeasurable).symm

end
end IGSIII34.Diffusion
