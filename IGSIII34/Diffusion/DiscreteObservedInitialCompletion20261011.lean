import IGSIII34.Diffusion.DiscreteRescaledObservationCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteWalkProperties

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory
open Universality.FiniteNetwork
open scoped NNReal

theorem discreteRescaledObservationLaw_initial_completion20261011
    {Vertex Edge Space : Type*} [Fintype Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    [MeasurableSpace Space]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (times : ℕ → ℝ≥0)
    (timeZero : times 0 = 0) (inclusion : Vertex → Space) :
    (discreteRescaledObservationLawCompletion20261011 endpoint positiveDegree initial scale times inclusion).map
      (measurable_pi_apply 0).aemeasurable = initial.map (measurable_of_finite inclusion).aemeasurable := by
  apply Subtype.ext
  change (Measure.map (discreteRescaledObservationCompletion20261011 scale times inclusion)
      (finiteDiscreteWalkLaw endpoint positiveDegree initial)).map (fun path => path 0) =
    (initial : Measure Vertex).map inclusion
  rw [Measure.map_map (measurable_pi_apply 0)
    (discreteRescaledObservation_measurable_completion20261011 scale times inclusion)]
  have zeroObservation : (fun path : ℕ → Space => path 0) ∘
      discreteRescaledObservationCompletion20261011 scale times inclusion =
      inclusion ∘ (fun path : ℕ → Vertex => path 0) := by
    funext path
    simp [Function.comp_apply, discreteRescaledObservationCompletion20261011, timeZero]
  rw [zeroObservation, ← Measure.map_map (measurable_of_finite inclusion) (measurable_pi_apply 0),
    finiteDiscreteWalkLaw_initial]

end
end IGSIII34.Diffusion
