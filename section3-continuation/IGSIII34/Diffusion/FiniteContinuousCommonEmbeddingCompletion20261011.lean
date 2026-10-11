import IGSIII34.Diffusion.CommonHoldingCadlagWeakCompletion20261011
import IGSIII34.Diffusion.ActualContinuousCadlagWholeWeakCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Universality
open scoped _root_.Topology NNReal

/-- The true exponential-holding finite walk laws transfer to a single
common spatial realization under uniform vertex-placement error. -/
theorem finiteContinuousCadlagProbability_common_embedding_weak_completion20261011
    {Target Ambient : Type*} [MetricSpace Target] [CompactSpace Target]
    [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Vertices Edges : ℕ → Type*) [∀ index, Fintype (Vertices index)] [∀ index, DecidableEq (Vertices index)]
    [∀ index, MeasurableSpace (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    [∀ index, Fintype (Edges index)]
    (endpoint : ∀ index, Edges index → Vertices index × Vertices index)
    (positiveDegree : ∀ index vertex, 0 < degree (endpoint index) vertex)
    (initial : ∀ index, ProbabilityMeasure (Vertices index))
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (targetEmbedding : Target → Ambient) (targetContinuous : Continuous targetEmbedding)
    (projections : ∀ index, Vertices index → Target)
    (placements : ∀ index, Vertices index → Ambient)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Target))
    (projectedWeak : Tendsto (fun index => finiteContinuousCadlagProbabilityCompletion20261011
      (endpoint index) (positiveDegree index) (initial index) (scales index) (scalesPositive index) (projections index))
      atTop (𝓝 law))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex, dist (placements index vertex) (targetEmbedding (projections index vertex)) < tolerance) :
    Tendsto (fun index => finiteContinuousCadlagProbabilityCompletion20261011
      (endpoint index) (positiveDegree index) (initial index) (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding
        targetContinuous).measurable.aemeasurable)) := by
  let laws := fun index => (⟨finiteContinuousWalkSampleLaw (endpoint index) (positiveDegree index)
    (initial index : Measure (Vertices index)), inferInstance⟩ : ProbabilityMeasure ((ℕ → Vertices index) × (ℕ → ℝ)))
  have regular (index : ℕ) : ∀ᵐ sample ∂(laws index : Measure ((ℕ → Vertices index) × (ℕ → ℝ))),
      (∀ jump, 0 < sample.2 jump) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop :=
    (finiteContinuousWalkSampleLaw_regular (endpoint index) (positiveDegree index)
      (initial index : Measure (Vertices index))).mono (fun _ clock => ⟨clock.1,clock.2.1⟩)
  exact holdingCadlagProbability_common_embedding_weak_completion20261011 Vertices laws regular scales scalesPositive
    targetEmbedding targetContinuous projections placements law projectedWeak placementClose

end
end IGSIII34.Diffusion
