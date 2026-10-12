import IGSIII34.Diffusion.CommonHoldingCadlagWeakCompletion
import IGSIII34.Diffusion.FiniteWeightedCadlagLawCompletion
import IGSIII34.Diffusion.FiniteCadlagSpatialMapCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Universality
open scoped _root_.Topology NNReal

theorem weightedHoldingCadlagProbability_common_embedding_weak_completion
    {Target Ambient : Type*} [MetricSpace Target] [CompactSpace Target]
    [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Vertices : ℕ → Type*) [∀ index, Fintype (Vertices index)] [∀ index, Nonempty (Vertices index)]
    [∀ index, MeasurableSpace (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    (laws : ∀ index, ProbabilityMeasure ((ℕ → Vertices index) × (ℕ → ℝ)))
    (weights : ∀ index, Vertices index → ℝ) (weightsPositive : ∀ index vertex, 0 < weights index vertex)
    (regular : ∀ index, ∀ᵐ sample ∂(laws index : Measure ((ℕ → Vertices index) × (ℕ → ℝ))),
      (∀ jump, 0 < sample.2 jump) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (targetEmbedding : Target → Ambient) (targetContinuous : Continuous targetEmbedding)
    (projections : ∀ index, Vertices index → Target) (placements : ∀ index, Vertices index → Ambient)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Target))
    (projectedWeak : Tendsto (fun index => weightedHoldingCadlagProbabilityCompletion
      (laws index) (weights index) (weightsPositive index) (regular index)
      (scales index) (scalesPositive index) (projections index)) atTop (𝓝 law))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex, dist (placements index vertex) (targetEmbedding (projections index vertex)) < tolerance) :
    Tendsto (fun index => weightedHoldingCadlagProbabilityCompletion
      (laws index) (weights index) (weightsPositive index) (regular index)
      (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion targetEmbedding
        targetContinuous).measurable.aemeasurable)) := by
  exact holdingCadlagProbability_common_embedding_weak_completion Vertices
    (fun index => (laws index).map (weightedHoldingSample_measurable_completion (weights index)).aemeasurable)
    (fun index => weightedHoldingSample_map_regular_completion (laws index) (weights index)
      (weightsPositive index) (regular index)) scales scalesPositive targetEmbedding targetContinuous
    projections placements law projectedWeak placementClose

theorem finiteWeightedCadlagProbability_common_embedding_weak_completion
    {Target Ambient : Type*} [MetricSpace Target] [CompactSpace Target]
    [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Vertices Edges : ℕ → Type*) [∀ index, Fintype (Vertices index)] [∀ index, Nonempty (Vertices index)]
    [∀ index, DecidableEq (Vertices index)] [∀ index, MeasurableSpace (Vertices index)]
    [∀ index, MeasurableSingletonClass (Vertices index)] [∀ index, Fintype (Edges index)]
    (endpoint : ∀ index, Edges index → Vertices index × Vertices index)
    (positiveDegree : ∀ index vertex, 0 < degree (endpoint index) vertex)
    (initial : ∀ index, ProbabilityMeasure (Vertices index))
    (weights : ∀ index, Vertices index → ℝ) (weightsPositive : ∀ index vertex, 0 < weights index vertex)
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (targetEmbedding : Target → Ambient) (targetContinuous : Continuous targetEmbedding)
    (projections : ∀ index, Vertices index → Target) (placements : ∀ index, Vertices index → Ambient)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Target))
    (projectedWeak : Tendsto (fun index => finiteWeightedCadlagProbabilityCompletion
      (endpoint index) (positiveDegree index) (initial index) (weights index) (weightsPositive index)
      (scales index) (scalesPositive index) (projections index)) atTop (𝓝 law))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex, dist (placements index vertex) (targetEmbedding (projections index vertex)) < tolerance) :
    Tendsto (fun index => finiteWeightedCadlagProbabilityCompletion
      (endpoint index) (positiveDegree index) (initial index) (weights index) (weightsPositive index)
      (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion targetEmbedding
        targetContinuous).measurable.aemeasurable)) := by
  exact weightedHoldingCadlagProbability_common_embedding_weak_completion Vertices
    (fun index => (⟨finiteContinuousWalkSampleLaw (endpoint index) (positiveDegree index)
      (initial index : Measure (Vertices index)), inferInstance⟩ : ProbabilityMeasure _))
    weights weightsPositive
    (fun index => (finiteContinuousWalkSampleLaw_regular (endpoint index) (positiveDegree index)
      (initial index : Measure (Vertices index))).mono (fun _ clock => ⟨clock.1, clock.2.1⟩))
    scales scalesPositive targetEmbedding targetContinuous projections placements law projectedWeak placementClose

theorem finiteWeightedCadlagProbability_spatial_map_completion
    {First Second Vertex Edge : Type*} [MetricSpace First] [CompactSpace First]
    [MetricSpace Second] [CompactSpace Second]
    [MeasurableSpace First] [BorelSpace First] [MeasurableSpace Second] [BorelSpace Second]
    [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    (homeomorph : First ≃ₜ Second) (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : ProbabilityMeasure Vertex)
    (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → First) :
    (finiteWeightedCadlagProbabilityCompletion endpoint positiveDegree initial weight weightPositive
      scale scalePositive placement).map
      (skorokhodCadlagCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable =
    finiteWeightedCadlagProbabilityCompletion endpoint positiveDegree initial weight weightPositive
      scale scalePositive (fun vertex => homeomorph (placement vertex)) :=
  holdingCadlagProbability_spatial_map_completion homeomorph
    (ProbabilityMeasure.map (⟨finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex), inferInstance⟩ : ProbabilityMeasure _)
      (weightedHoldingSample_measurable_completion weight).aemeasurable)
    (weightedHoldingSample_map_regular_completion
      (⟨finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex), inferInstance⟩ : ProbabilityMeasure _)
      weight weightPositive ((finiteContinuousWalkSampleLaw_regular endpoint positiveDegree (initial : Measure Vertex)).mono
        (fun _ clock => ⟨clock.1, clock.2.1⟩))) scale scalePositive placement

end
end IGSIII34.Diffusion