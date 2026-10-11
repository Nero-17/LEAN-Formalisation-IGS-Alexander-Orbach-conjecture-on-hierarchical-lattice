import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion20261011
import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal

theorem holdingCadlagSample_placement_close_completion20261011
    {Vertex Target Ambient : Type*}
    [MetricSpace Target] [CompactSpace Target] [MetricSpace Ambient] [CompactSpace Ambient]
    (targetEmbedding : Target → Ambient) (projection : Vertex → Target) (placement : Vertex → Ambient)
    (scale : ℝ) (scalePositive : 0 < scale) (tolerance : ℝ)
    (close : ∀ vertex, dist (placement vertex) (targetEmbedding (projection vertex)) < tolerance)
    (outcome : (ℕ → Vertex) × (ℕ → ℝ)) (time : ℝ≥0) :
    dist ((holdingCadlagSampleCompletion20261011 scale scalePositive placement outcome).val time)
      (targetEmbedding ((holdingCadlagSampleCompletion20261011 scale scalePositive projection outcome).val time)) < tolerance := by
  classical
  by_cases regular : (∀ index, 0 < outcome.2 index) ∧ Tendsto (cumulativeHoldingTime outcome.2) atTop atTop
  · simpa only [holdingCadlagSampleCompletion20261011, dif_pos regular,
      holdingGlobalSkorokhodSampleCompletion20261011] using
      close (holdingTimePath outcome.1 outcome.2 (scale * (time:ℝ)))
  · simpa only [holdingCadlagSampleCompletion20261011, dif_neg regular] using close (outcome.1 0)

/-- The original holding path law, including the same measurable null-set
repair, transfers from its projected carrier to the common isometric
realization. It also applies to dependent positive holding-clock laws. -/
theorem holdingCadlagProbability_common_embedding_weak_completion20261011
    {Target Ambient : Type*} [MetricSpace Target] [CompactSpace Target]
    [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Vertices : ℕ → Type*) [∀ index, Fintype (Vertices index)]
    [∀ index, MeasurableSpace (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    (laws : ∀ index, ProbabilityMeasure ((ℕ → Vertices index) × (ℕ → ℝ)))
    (regular : ∀ index, ∀ᵐ sample ∂(laws index : Measure ((ℕ → Vertices index) × (ℕ → ℝ))),
      (∀ jump, 0 < sample.2 jump) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (targetEmbedding : Target → Ambient) (targetContinuous : Continuous targetEmbedding)
    (projections : ∀ index, Vertices index → Target)
    (placements : ∀ index, Vertices index → Ambient)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Target))
    (projectedWeak : Tendsto (fun index => holdingCadlagProbabilityCompletion20261011
      (laws index) (regular index) (scales index) (scalesPositive index) (projections index)) atTop (𝓝 law))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex, dist (placements index vertex) (targetEmbedding (projections index vertex)) < tolerance) :
    Tendsto (fun index => holdingCadlagProbabilityCompletion20261011
      (laws index) (regular index) (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding
        targetContinuous).measurable.aemeasurable)) := by
  apply common_embedding_cadlag_sample_weak_completion20261011
    (fun index => ((ℕ → Vertices index) × (ℕ → ℝ)))
    (fun index => (laws index : Measure ((ℕ → Vertices index) × (ℕ → ℝ)))) targetEmbedding targetContinuous
    (fun index => holdingCadlagSampleCompletion20261011 (scales index) (scalesPositive index) (placements index))
    (fun index => holdingCadlagSampleCompletion20261011 (scales index) (scalesPositive index) (projections index))
    (fun index => holdingCadlagSample_aemeasurable_completion20261011 _ (regular index) _ _ _)
    (fun index => holdingCadlagSample_aemeasurable_completion20261011 _ (regular index) _ _ _)
    law projectedWeak
  intro tolerance positive
  filter_upwards [placementClose tolerance positive] with index close
  exact holdingCadlagSample_placement_close_completion20261011 targetEmbedding (projections index)
    (placements index) (scales index) (scalesPositive index) tolerance close

end
end IGSIII34.Diffusion
