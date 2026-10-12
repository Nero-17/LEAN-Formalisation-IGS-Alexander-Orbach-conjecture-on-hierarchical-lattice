import IGSIII34.Diffusion.FiniteWeightedGlobalWeakCompletion
import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def weightedHoldingCadlagProbabilityCompletion
    {Vertex : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [Nonempty Vertex] [MeasurableSingletonClass Vertex]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion Space) :=
  holdingCadlagProbabilityCompletion
    (law.map (weightedHoldingSample_measurable_completion weight).aemeasurable)
    (weightedHoldingSample_map_regular_completion law weight weightPositive regular)
    scale scalePositive placement

theorem weightedHoldingCadlagProbability_val_completion
    {Vertex : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [Nonempty Vertex] [MeasurableSingletonClass Vertex]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (weightedHoldingCadlagProbabilityCompletion law weight weightPositive regular scale scalePositive placement).map
      measurable_subtype_coe.aemeasurable =
    law.map (weightedHoldingGlobalSample_aemeasurable_completion law weight weightPositive regular scale scalePositive placement) := by
  unfold weightedHoldingCadlagProbabilityCompletion
  rw [holdingCadlagProbability_val_completion]
  apply Subtype.ext
  exact AEMeasurable.map_map_of_aemeasurable
    (holdingGlobalSkorokhodSample_aemeasurable_completion _
      (weightedHoldingSample_map_regular_completion law weight weightPositive regular) scale scalePositive placement)
    (weightedHoldingSample_measurable_completion weight).aemeasurable

theorem weightedHoldingCadlagProbability_weak_of_global_weak_completion
    (Vertices : ℕ → Type*) [∀ depth, MeasurableSpace (Vertices depth)]
    [∀ depth, Fintype (Vertices depth)] [∀ depth, Nonempty (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    (laws : ∀ depth, ProbabilityMeasure ((ℕ → Vertices depth) × (ℕ → ℝ)))
    (weights : ∀ depth, Vertices depth → ℝ) (positive : ∀ depth vertex, 0 < weights depth vertex)
    (regular : ∀ depth, ∀ᵐ sample ∂(laws depth : Measure ((ℕ → Vertices depth) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scales : ℕ → ℝ) (scalesPositive : ∀ depth, 0 < scales depth) (placements : ∀ depth, Vertices depth → Space)
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (weak : Tendsto (fun depth => (laws depth).map
      (weightedHoldingGlobalSample_aemeasurable_completion (laws depth) (weights depth) (positive depth)
        (regular depth) (scales depth) (scalesPositive depth) (placements depth))) atTop
      (𝓝 (law.map (continuousGlobalFamily_measurable_completion sample continuous evaluations).aemeasurable))) :
    Tendsto (fun depth => weightedHoldingCadlagProbabilityCompletion (laws depth) (weights depth) (positive depth)
      (regular depth) (scales depth) (scalesPositive depth) (placements depth)) atTop
      (𝓝 (continuousCadlagProbabilityCompletion law sample continuous evaluations)) := by
  apply probability_subtype_weak_of_val_weak_completion
    (fun path : SkorokhodGlobalPathCompletion Space => SkorokhodCadlagCompletion path)
  simpa only [weightedHoldingCadlagProbability_val_completion,
    continuousCadlagProbability_val_completion] using weak

end
end IGSIII34.Diffusion
