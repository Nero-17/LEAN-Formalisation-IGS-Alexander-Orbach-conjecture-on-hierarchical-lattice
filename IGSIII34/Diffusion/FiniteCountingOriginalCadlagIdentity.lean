import IGSIII34.Diffusion.FiniteWeightedCadlagLawCompletion20261011
import IGSIII34.Diffusion.WeightedClockRateIdentificationCompletion20261011
import IGSIII34.Diffusion.ProbabilitySubtypeIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory
open scoped NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  {Vertex Edge : Type*} [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge] [Nonempty Edge]

/-- Exact equality of the whole cadlag laws of the normalized counting clock
and the original inverse-degree holding-time clock, in any compact placement. -/
theorem finiteCountingOriginalCadlagIdentity
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (scalePositive : 0 < scale)
    (placement : Vertex → Space) :
    finiteWeightedCadlagProbabilityCompletion20261011 endpoint positiveDegree initial
      (finiteCountingClockDensityCompletion20261011 endpoint)
      (finiteCountingClockDensity_positive_completion20261011 endpoint positiveDegree)
      ((2 * Fintype.card Edge : ℝ) * scale) (by positivity) placement =
    finiteWeightedCadlagProbabilityCompletion20261011 endpoint positiveDegree initial
      (fun vertex => (degree endpoint vertex)⁻¹) (fun vertex => inv_pos.mpr (positiveDegree vertex))
      ((Fintype.card Vertex : ℝ) * scale) (by positivity) placement := by
  apply probability_subtype_val_map_injective
  dsimp only
  rw [finiteWeightedCadlagProbability_val_completion20261011,
    finiteWeightedCadlagProbability_val_completion20261011]
  apply ProbabilityMeasure.toMeasure_injective
  change (finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex)).map
      (weightedHoldingGlobalSampleCompletion20261011
        (finiteCountingClockDensityCompletion20261011 endpoint) ((2 * Fintype.card Edge : ℝ) * scale) placement) =
    (finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex)).map
      (weightedHoldingGlobalSampleCompletion20261011
        (fun vertex => (degree endpoint vertex)⁻¹) ((Fintype.card Vertex : ℝ) * scale) placement)
  apply Measure.map_congr
  filter_upwards [finiteCountingClockDensity_vertex_clock_identity_completion20261011
    endpoint positiveDegree initial scale scalePositive] with sample equality
  apply congrArg SkorokhodGlobalPathCompletion20261011.mk
  funext time
  apply congrArg placement
  simpa only [weightedHoldingGlobalSampleCompletion20261011,
    holdingGlobalSkorokhodSampleCompletion20261011, weightedHoldingSampleCompletion20261011,
    div_eq_mul_inv, mul_comm] using equality (time : ℝ) time.property

theorem finiteCountingOriginalCadlagIdentity_arbitrary_clock
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (clock : ℝ) (clockPositive : 0 < clock)
    (placement : Vertex → Space) :
    finiteWeightedCadlagProbabilityCompletion20261011 endpoint positiveDegree initial
      (finiteCountingClockDensityCompletion20261011 endpoint)
      (finiteCountingClockDensity_positive_completion20261011 endpoint positiveDegree)
      clock clockPositive placement =
    finiteWeightedCadlagProbabilityCompletion20261011 endpoint positiveDegree initial
      (fun vertex => (degree endpoint vertex)⁻¹) (fun vertex => inv_pos.mpr (positiveDegree vertex))
      (((Fintype.card Vertex : ℝ) / (2 * Fintype.card Edge : ℝ)) * clock)
      (by positivity) placement := by
  have firstClock : (2 * Fintype.card Edge : ℝ) * (clock / (2 * Fintype.card Edge : ℝ)) = clock := by
    field_simp
  have lastClock : (Fintype.card Vertex : ℝ) * (clock / (2 * Fintype.card Edge : ℝ)) =
      ((Fintype.card Vertex : ℝ) / (2 * Fintype.card Edge : ℝ)) * clock := by ring
  simpa only [firstClock, lastClock] using finiteCountingOriginalCadlagIdentity
    endpoint positiveDegree initial (clock / (2 * Fintype.card Edge : ℝ)) (by positivity) placement

end
end IGSIII34.Diffusion
