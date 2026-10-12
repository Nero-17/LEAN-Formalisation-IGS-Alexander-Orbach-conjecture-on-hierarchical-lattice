import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion
import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

def discreteCadlagProbabilityCompletion
    {Vertex Space : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : ProbabilityMeasure (ℕ → Vertex)) (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion Space) :=
  law.map (discreteCadlagSample_measurable_completion scale scalePositive placement).aemeasurable

theorem discreteCadlagProbability_val_completion
    {Vertex Space : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : ProbabilityMeasure (ℕ → Vertex)) (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (discreteCadlagProbabilityCompletion law scale scalePositive placement).map measurable_subtype_coe.aemeasurable =
    law.map (discreteGlobalSkorokhodSample_measurable_completion scale scalePositive.le placement).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure (ℕ → Vertex)).map (discreteCadlagSampleCompletion scale scalePositive placement)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe (discreteCadlagSample_measurable_completion scale scalePositive placement)]
  rfl

theorem discreteCadlagProbability_weak_of_global_weak_completion
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (Vertices : ℕ → Type*) [∀ index, MeasurableSpace (Vertices index)]
    [∀ index, Fintype (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    (laws : ∀ index, ProbabilityMeasure (ℕ → Vertices index))
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (placements : ∀ index, Vertices index → Space)
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (weak : Tendsto (fun index => (laws index).map
      (discreteGlobalSkorokhodSample_measurable_completion (scales index) (scalesPositive index).le
        (placements index)).aemeasurable) atTop
      (𝓝 (law.map (continuousGlobalFamily_measurable_completion sample continuous evaluations).aemeasurable))) :
    Tendsto (fun index => discreteCadlagProbabilityCompletion (laws index)
      (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (continuousCadlagProbabilityCompletion law sample continuous evaluations)) := by
  apply probability_subtype_weak_of_val_weak_completion
    (fun path : SkorokhodGlobalPathCompletion Space => SkorokhodCadlagCompletion path)
  simpa only [discreteCadlagProbability_val_completion, continuousCadlagProbability_val_completion] using weak

/-- Original discrete sample laws, rather than just their observations,
transfer to the common space under uniform vertex placement error. -/
theorem discreteCadlagProbability_common_embedding_weak_completion
    {Target Ambient : Type*} [MetricSpace Target] [CompactSpace Target]
    [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Vertices : ℕ → Type*) [∀ index, Fintype (Vertices index)]
    [∀ index, MeasurableSpace (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    (laws : ∀ index, ProbabilityMeasure (ℕ → Vertices index))
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (targetEmbedding : Target → Ambient) (targetContinuous : Continuous targetEmbedding)
    (projections : ∀ index, Vertices index → Target) (placements : ∀ index, Vertices index → Ambient)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Target))
    (projectedWeak : Tendsto (fun index => discreteCadlagProbabilityCompletion
      (laws index) (scales index) (scalesPositive index) (projections index)) atTop (𝓝 law))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex, dist (placements index vertex) (targetEmbedding (projections index vertex)) < tolerance) :
    Tendsto (fun index => discreteCadlagProbabilityCompletion
      (laws index) (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion targetEmbedding
        targetContinuous).measurable.aemeasurable)) := by
  apply common_embedding_cadlag_sample_weak_completion
    (fun index => ℕ → Vertices index) (fun index => (laws index : Measure (ℕ → Vertices index)))
    targetEmbedding targetContinuous
    (fun index => discreteCadlagSampleCompletion (scales index) (scalesPositive index) (placements index))
    (fun index => discreteCadlagSampleCompletion (scales index) (scalesPositive index) (projections index))
    (fun index => (discreteCadlagSample_measurable_completion _ _ _).aemeasurable)
    (fun index => (discreteCadlagSample_measurable_completion _ _ _).aemeasurable)
    law projectedWeak
  intro tolerance positive
  filter_upwards [placementClose tolerance positive] with index close
  intro outcome time
  exact close (outcome ⌊scales index * (time:ℝ)⌋₊)

end
end IGSIII34.Diffusion
