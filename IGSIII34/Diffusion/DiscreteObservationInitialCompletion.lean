import IGSIII34.Diffusion.DiscreteRescaledObservationCompletion
import IGSIII34.Diffusion.ActualDiscreteWalkProperties

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology NNReal

variable {Vertex Edge Space : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [MeasurableSpace Space]

theorem discreteRescaledObservation_initial_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (times : ℕ → ℝ≥0) (inclusion : Vertex → Space)
    (coordinate : ℕ) (timeZero : times coordinate = 0) :
    (discreteRescaledObservationLawCompletion endpoint positiveDegree initial scale times inclusion).map
      (measurable_pi_apply coordinate).aemeasurable = initial.map (measurable_of_finite inclusion).aemeasurable := by
  apply Subtype.ext
  change ((finiteDiscreteWalkLaw endpoint positiveDegree (initial : Measure Vertex)).map
    (discreteRescaledObservationCompletion scale times inclusion)).map (fun path : ℕ → Space => path coordinate) =
      (initial : Measure Vertex).map inclusion
  rw [Measure.map_map (measurable_pi_apply coordinate)
    (discreteRescaledObservation_measurable_completion scale times inclusion)]
  have composed : ((fun path : ℕ → Space => path coordinate) ∘ discreteRescaledObservationCompletion scale times inclusion) =
      inclusion ∘ (fun path : ℕ → Vertex => path 0) := by
    funext path
    simp only [Function.comp_apply, discreteRescaledObservationCompletion, timeZero, NNReal.coe_zero, mul_zero, Nat.floor_zero]
  rw [composed, ← Measure.map_map (measurable_of_finite inclusion) (measurable_pi_apply 0), finiteDiscreteWalkLaw_initial]

theorem discreteRescaledObservation_limit_initial_completion
    [MetricSpace Space] [CompactSpace Space] [BorelSpace Space]
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth)) (scale : ℕ → ℝ) (times : ℕ → ℝ≥0)
    (inclusion : ∀ depth, Vertices depth → Space)
    (limitLaw : ProbabilityMeasure (ℕ → Space))
    (weak : Tendsto (fun depth => discreteRescaledObservationLawCompletion (endpoint depth) (positiveDegree depth)
      (initial depth) (scale depth) times (inclusion depth)) atTop (𝓝 limitLaw))
    (initialLimit : ProbabilityMeasure Space)
    (initialConvergence : Tendsto (fun depth => (initial depth).map (measurable_of_finite (inclusion depth)).aemeasurable) atTop (𝓝 initialLimit))
    (coordinate : ℕ) (timeZero : times coordinate = 0) :
    limitLaw.map (measurable_pi_apply coordinate).aemeasurable = initialLimit := by
  have coordinateLimit := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ weak (continuous_apply coordinate)
  have initialLimitSame := coordinateLimit.congr' (Eventually.of_forall fun depth =>
    discreteRescaledObservation_initial_completion (endpoint depth) (positiveDegree depth) (initial depth)
      (scale depth) times (inclusion depth) coordinate timeZero)
  exact tendsto_nhds_unique initialLimitSame initialConvergence

end
end IGSIII34.Diffusion

