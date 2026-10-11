import IGSIII34.Diffusion.CountableTimeLimitsCompletion20261011
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology NNReal

variable {Vertex Edge Space : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [MeasurableSpace Space]

def discreteRescaledObservationCompletion20261011 (scale : ℝ) (times : ℕ → ℝ≥0)
    (inclusion : Vertex → Space) (path : ℕ → Vertex) : ℕ → Space :=
  fun coordinate => inclusion (path ⌊scale * (times coordinate : ℝ)⌋₊)

theorem discreteRescaledObservation_measurable_completion20261011 (scale : ℝ) (times : ℕ → ℝ≥0)
    (inclusion : Vertex → Space) : Measurable (discreteRescaledObservationCompletion20261011 scale times inclusion) := by
  apply measurable_pi_lambda
  intro coordinate
  exact (measurable_of_finite inclusion).comp (measurable_pi_apply _)

def discreteWalkProbabilityCompletion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) : ProbabilityMeasure (ℕ → Vertex) :=
  ⟨finiteDiscreteWalkLaw endpoint positiveDegree initial, by infer_instance⟩

def discreteRescaledObservationLawCompletion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (times : ℕ → ℝ≥0) (inclusion : Vertex → Space) : ProbabilityMeasure (ℕ → Space) :=
  (discreteWalkProbabilityCompletion20261011 endpoint positiveDegree initial).map
    (discreteRescaledObservation_measurable_completion20261011 scale times inclusion).aemeasurable

end
end IGSIII34.Diffusion
