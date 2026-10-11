import IGSIII34.Diffusion.UsualLocalJ1WeakTests
import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

variable {First Second Outcome : Type*}
  [MetricSpace First] [CompactSpace First] [MeasurableSpace First] [BorelSpace First]
  [MetricSpace Second] [CompactSpace Second] [MeasurableSpace Second] [BorelSpace Second]
  [MeasurableSpace Outcome]

/-- Continuous sample laws commute exactly with a continuous spatial map.
This permits weak-test passage in the common chemical realization, including
the actual isometric embeddings of the finite clusters. -/
theorem continuousCadlagProbability_spatial_map
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → First)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (spatial : First → Second) (spatialContinuous : Continuous spatial) :
    (continuousCadlagProbabilityCompletion20261011 law sample continuous evaluations).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 spatial spatialContinuous).measurable.aemeasurable =
    continuousCadlagProbabilityCompletion20261011 law
      (fun outcome time => spatial (sample outcome time))
      (fun outcome => spatialContinuous.comp (continuous outcome))
      (fun time => spatialContinuous.measurable.comp (evaluations time)) := by
  apply Subtype.ext
  change ((law : Measure Outcome).map (continuousCadlagSampleCompletion20261011 sample continuous)).map
    (skorokhodCadlagContinuousCarrierMapCompletion20261011 spatial spatialContinuous) = _
  rw [Measure.map_map
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 spatial spatialContinuous).measurable
    (continuousCadlagSample_measurable_completion20261011 sample continuous evaluations)]
  rfl

/-- The usual-local J1 weak tests also hold after the actual continuous
chemical-carrier embedding. The conclusion is about the placed original
law and its transported continuous limit, rather than only canonical born
vertices in the electrical carrier. -/
theorem skorokhodCadlag_spatial_weak_usualLocalJ1_tests_continuousSample
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Second))
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → First)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (spatial : First → Second) (spatialContinuous : Continuous spatial)
    (weak : Tendsto laws atTop
      (𝓝 ((continuousCadlagProbabilityCompletion20261011 law sample continuous evaluations).map
        (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 spatial spatialContinuous).measurable.aemeasurable))) :
    usualLocalJ1WeakTestConvergence laws
      ((continuousCadlagProbabilityCompletion20261011 law sample continuous evaluations).map
        (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 spatial spatialContinuous).measurable.aemeasurable) := by
  rw [continuousCadlagProbability_spatial_map] at weak ⊢
  exact skorokhodCadlag_weak_usualLocalJ1_tests_continuousSample laws law
    (fun outcome time => spatial (sample outcome time))
    (fun outcome => spatialContinuous.comp (continuous outcome))
    (fun time => spatialContinuous.measurable.comp (evaluations time)) weak

end
end IGSIII34.Diffusion
