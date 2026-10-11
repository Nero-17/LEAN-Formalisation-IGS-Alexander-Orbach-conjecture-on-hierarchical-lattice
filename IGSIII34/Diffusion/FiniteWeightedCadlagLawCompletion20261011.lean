import IGSIII34.Diffusion.WeightedCadlagWeakCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def finiteWeightedCadlagProbabilityCompletion20261011
    {Vertex Edge : Type*} [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space) :=
  weightedHoldingCadlagProbabilityCompletion20261011
    (⟨finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex), inferInstance⟩ : ProbabilityMeasure _)
    weight weightPositive
    ((finiteContinuousWalkSampleLaw_regular endpoint positiveDegree (initial : Measure Vertex)).mono
      (fun _ regular => ⟨regular.1, regular.2.1⟩)) scale scalePositive placement

theorem finiteWeightedCadlagProbability_val_completion20261011
    {Vertex Edge : Type*} [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (finiteWeightedCadlagProbabilityCompletion20261011 endpoint positiveDegree initial weight weightPositive scale scalePositive placement).map
      measurable_subtype_coe.aemeasurable =
      finiteWeightedGlobalSkorokhodProbabilityCompletion20261011 endpoint positiveDegree initial weight weightPositive scale scalePositive placement := by
  exact weightedHoldingCadlagProbability_val_completion20261011 _ _ _ _ _ _ _

end
end IGSIII34.Diffusion
