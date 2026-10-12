import IGSIII34.Diffusion.SkorokhodCadlagCarrierTransportCompletion
import IGSIII34.Diffusion.ActualContinuousCadlagWholeWeakCompletion

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

theorem holdingCadlagSample_spatial_map_completion
    (homeomorph : First ≃ₜ Second) (scale : ℝ) (scalePositive : 0 < scale)
    (placement : Vertex → First) (sample : (ℕ → Vertex) × (ℕ → ℝ)) :
    skorokhodCadlagCarrierHomeomorphCompletion homeomorph
      (holdingCadlagSampleCompletion scale scalePositive placement sample) =
    holdingCadlagSampleCompletion scale scalePositive (fun vertex => homeomorph (placement vertex)) sample := by
  classical
  apply Subtype.ext
  by_cases regular : (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop
  · simp only [skorokhodCadlagCarrierHomeomorphCompletion, holdingCadlagSampleCompletion, dif_pos regular]
    rfl
  · simp only [skorokhodCadlagCarrierHomeomorphCompletion, holdingCadlagSampleCompletion, dif_neg regular]
    rfl

theorem holdingCadlagProbability_spatial_map_completion
    (homeomorph : First ≃ₜ Second)
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → First) :
    (holdingCadlagProbabilityCompletion law regular scale scalePositive placement).map
      (skorokhodCadlagCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable =
    holdingCadlagProbabilityCompletion law regular scale scalePositive (fun vertex => homeomorph (placement vertex)) := by
  apply Subtype.ext
  change ((law : Measure ((ℕ → Vertex) × (ℕ → ℝ))).map
    (holdingCadlagSampleCompletion scale scalePositive placement)).map
      (skorokhodCadlagCarrierHomeomorphCompletion homeomorph) = _
  rw [AEMeasurable.map_map_of_aemeasurable
    (skorokhodCadlagCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable
    (holdingCadlagSample_aemeasurable_completion (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement)]
  exact Measure.map_congr (Eventually.of_forall
    (holdingCadlagSample_spatial_map_completion homeomorph scale scalePositive placement))

theorem finiteContinuousCadlagProbability_spatial_map_completion
    [DecidableEq Vertex] [Fintype Edge]
    (homeomorph : First ≃ₜ Second) (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : ProbabilityMeasure Vertex)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → First) :
    (finiteContinuousCadlagProbabilityCompletion endpoint positiveDegree initial scale scalePositive placement).map
      (skorokhodCadlagCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable =
    finiteContinuousCadlagProbabilityCompletion endpoint positiveDegree initial scale scalePositive
      (fun vertex => homeomorph (placement vertex)) :=
  holdingCadlagProbability_spatial_map_completion homeomorph _ _ scale scalePositive placement

end
end IGSIII34.Diffusion
