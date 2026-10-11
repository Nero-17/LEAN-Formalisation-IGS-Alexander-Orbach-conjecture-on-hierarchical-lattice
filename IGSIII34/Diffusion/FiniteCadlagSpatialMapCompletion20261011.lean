import IGSIII34.Diffusion.SkorokhodCadlagCarrierTransportCompletion20261011
import IGSIII34.Diffusion.ActualContinuousCadlagWholeWeakCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {First Second Vertex Edge : Type*} [MetricSpace First] [CompactSpace First]
  [MetricSpace Second] [CompactSpace Second]
  [MeasurableSpace First] [BorelSpace First] [MeasurableSpace Second] [BorelSpace Second]
  [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]

theorem holdingCadlagSample_spatial_map_completion20261011
    (homeomorph : First ≃ₜ Second) (scale : ℝ) (scalePositive : 0 < scale)
    (placement : Vertex → First) (sample : (ℕ → Vertex) × (ℕ → ℝ)) :
    skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph
      (holdingCadlagSampleCompletion20261011 scale scalePositive placement sample) =
    holdingCadlagSampleCompletion20261011 scale scalePositive (fun vertex => homeomorph (placement vertex)) sample := by
  classical
  apply Subtype.ext
  by_cases regular : (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop
  · simp only [skorokhodCadlagCarrierHomeomorphCompletion20261011, holdingCadlagSampleCompletion20261011, dif_pos regular]
    rfl
  · simp only [skorokhodCadlagCarrierHomeomorphCompletion20261011, holdingCadlagSampleCompletion20261011, dif_neg regular]
    rfl

theorem holdingCadlagProbability_spatial_map_completion20261011
    (homeomorph : First ≃ₜ Second)
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → First) :
    (holdingCadlagProbabilityCompletion20261011 law regular scale scalePositive placement).map
      (skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph).continuous.measurable.aemeasurable =
    holdingCadlagProbabilityCompletion20261011 law regular scale scalePositive (fun vertex => homeomorph (placement vertex)) := by
  apply Subtype.ext
  change ((law : Measure ((ℕ → Vertex) × (ℕ → ℝ))).map
    (holdingCadlagSampleCompletion20261011 scale scalePositive placement)).map
      (skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph) = _
  rw [AEMeasurable.map_map_of_aemeasurable
    (skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph).continuous.measurable.aemeasurable
    (holdingCadlagSample_aemeasurable_completion20261011 (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement)]
  exact Measure.map_congr (Eventually.of_forall
    (holdingCadlagSample_spatial_map_completion20261011 homeomorph scale scalePositive placement))

theorem finiteContinuousCadlagProbability_spatial_map_completion20261011
    [DecidableEq Vertex] [Fintype Edge]
    (homeomorph : First ≃ₜ Second) (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : ProbabilityMeasure Vertex)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → First) :
    (finiteContinuousCadlagProbabilityCompletion20261011 endpoint positiveDegree initial scale scalePositive placement).map
      (skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph).continuous.measurable.aemeasurable =
    finiteContinuousCadlagProbabilityCompletion20261011 endpoint positiveDegree initial scale scalePositive
      (fun vertex => homeomorph (placement vertex)) :=
  holdingCadlagProbability_spatial_map_completion20261011 homeomorph _ _ scale scalePositive placement

end
end IGSIII34.Diffusion
