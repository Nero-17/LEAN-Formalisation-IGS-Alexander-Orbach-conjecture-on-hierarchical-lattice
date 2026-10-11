import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion20261011
import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

def discreteCadlagProbabilityCompletion20261011
    {Vertex Space : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : ProbabilityMeasure (ℕ → Vertex)) (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space) :=
  law.map (discreteCadlagSample_measurable_completion20261011 scale scalePositive placement).aemeasurable

theorem discreteCadlagProbability_val_completion20261011
    {Vertex Space : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : ProbabilityMeasure (ℕ → Vertex)) (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (discreteCadlagProbabilityCompletion20261011 law scale scalePositive placement).map measurable_subtype_coe.aemeasurable =
    law.map (discreteGlobalSkorokhodSample_measurable_completion20261011 scale scalePositive.le placement).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure (ℕ → Vertex)).map (discreteCadlagSampleCompletion20261011 scale scalePositive placement)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe (discreteCadlagSample_measurable_completion20261011 scale scalePositive placement)]
  rfl

theorem discreteCadlagProbability_weak_of_global_weak_completion20261011
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
      (discreteGlobalSkorokhodSample_measurable_completion20261011 (scales index) (scalesPositive index).le
        (placements index)).aemeasurable) atTop
      (𝓝 (law.map (continuousGlobalFamily_measurable_completion20261011 sample continuous evaluations).aemeasurable))) :
    Tendsto (fun index => discreteCadlagProbabilityCompletion20261011 (laws index)
      (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (continuousCadlagProbabilityCompletion20261011 law sample continuous evaluations)) := by
  apply probability_subtype_weak_of_val_weak_completion20261011
    (fun path : SkorokhodGlobalPathCompletion20261011 Space => SkorokhodCadlagCompletion20261011 path)
  simpa only [discreteCadlagProbability_val_completion20261011, continuousCadlagProbability_val_completion20261011] using weak

/-- Original discrete sample laws, rather than just their observations,
transfer to the common space under uniform vertex placement error. -/
theorem discreteCadlagProbability_common_embedding_weak_completion20261011
    {Target Ambient : Type*} [MetricSpace Target] [CompactSpace Target]
    [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Vertices : ℕ → Type*) [∀ index, Fintype (Vertices index)]
    [∀ index, MeasurableSpace (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    (laws : ∀ index, ProbabilityMeasure (ℕ → Vertices index))
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (targetEmbedding : Target → Ambient) (targetContinuous : Continuous targetEmbedding)
    (projections : ∀ index, Vertices index → Target) (placements : ∀ index, Vertices index → Ambient)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Target))
    (projectedWeak : Tendsto (fun index => discreteCadlagProbabilityCompletion20261011
      (laws index) (scales index) (scalesPositive index) (projections index)) atTop (𝓝 law))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex, dist (placements index vertex) (targetEmbedding (projections index vertex)) < tolerance) :
    Tendsto (fun index => discreteCadlagProbabilityCompletion20261011
      (laws index) (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding
        targetContinuous).measurable.aemeasurable)) := by
  apply common_embedding_cadlag_sample_weak_completion20261011
    (fun index => ℕ → Vertices index) (fun index => (laws index : Measure (ℕ → Vertices index)))
    targetEmbedding targetContinuous
    (fun index => discreteCadlagSampleCompletion20261011 (scales index) (scalesPositive index) (placements index))
    (fun index => discreteCadlagSampleCompletion20261011 (scales index) (scalesPositive index) (projections index))
    (fun index => (discreteCadlagSample_measurable_completion20261011 _ _ _).aemeasurable)
    (fun index => (discreteCadlagSample_measurable_completion20261011 _ _ _).aemeasurable)
    law projectedWeak
  intro tolerance positive
  filter_upwards [placementClose tolerance positive] with index close
  intro outcome time
  exact close (outcome ⌊scales index * (time:ℝ)⌋₊)

end
end IGSIII34.Diffusion
