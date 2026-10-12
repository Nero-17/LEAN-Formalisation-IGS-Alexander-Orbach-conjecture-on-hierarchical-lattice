import IGSIII34.Diffusion.FiniteWeightedCadlagLawCompletion
import IGSIII34.Diffusion.ActualContinuousCadlagWholeWeakCompletion
import IGSIII34.Diffusion.ProbabilitySubtypeIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory

/-- Unit holding weights give exactly the original rate-one entire cadlag law. -/
theorem finiteUnitWeightCadlagIdentity
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    {Vertex Edge : Type*} [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (clock : ℝ) (clockPositive : 0 < clock)
    (placement : Vertex → Space) :
    finiteWeightedCadlagProbabilityCompletion endpoint positiveDegree initial
      (fun _ => 1) (fun _ => zero_lt_one) clock clockPositive placement =
    finiteContinuousCadlagProbabilityCompletion endpoint positiveDegree initial
      clock clockPositive placement := by
  apply probability_subtype_val_map_injective
  dsimp only
  rw [finiteWeightedCadlagProbability_val_completion,
    finiteContinuousCadlagProbability_val_completion]
  apply ProbabilityMeasure.toMeasure_injective
  change (finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex)).map
      (weightedHoldingGlobalSampleCompletion (fun _ => 1) clock placement) =
    (finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex)).map
      (holdingGlobalSkorokhodSampleCompletion clock placement)
  congr 1
  funext sample
  simp only [weightedHoldingGlobalSampleCompletion, weightedHoldingSampleCompletion, one_mul]

end
end IGSIII34.Diffusion
