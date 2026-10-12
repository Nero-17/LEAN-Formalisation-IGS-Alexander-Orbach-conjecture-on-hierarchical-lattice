import IGSIII34.Diffusion.OriginalJointUsualWeakSample
import IGSIII34.Diffusion.OriginalJointCompactPathLaw
import IGSIII34.Diffusion.UsualLocalJ1SpatialWeakTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

/-- The law gives full mass to continuity points of every usual joint
test. No sigma algebra on the set of continuous representatives is used. -/
def OriginalJointUsualTestRegular (law : ProbabilityMeasure OriginalJointCompactSpace) : Prop :=
  ∀ test : OriginalJointCompactSpace → ℝ,
    OriginalJointUsualSequentiallyContinuousTest test →
      ∀ᵐ point ∂(law : Measure OriginalJointCompactSpace), ContinuousAt test point

theorem originalJointContinuousSampleLaw_regular
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome)
    (sample : Outcome → OriginalJointCompactRepresentative)
    (measurable : Measurable (fun outcome => originalJointCompactClass (sample outcome)))
    (continuous : ∀ outcome, Continuous (sample outcome).path.val.toFun) :
    OriginalJointUsualTestRegular (law.map measurable.aemeasurable) := by
  intro test usualContinuous
  change ∀ᵐ point ∂(law : Measure Outcome).map
    (fun outcome => originalJointCompactClass (sample outcome)), ContinuousAt test point
  rw [ae_map_iff measurable.aemeasurable (measurableSet_of_continuousAt test)]
  exact Eventually.of_forall (fun outcome =>
    originalJointUsualTest_continuousAt_continuous_representative test usualContinuous
      (sample outcome) (continuous outcome))

theorem originalJointCompactRepresentative_ofCompactSpace_continuous
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (path : SkorokhodCadlagPathCompletion Space)
    (continuous : Continuous path.val.toFun) :
    Continuous (OriginalJointCompactRepresentative.ofCompactSpace marks masses path).path.val.toFun := by
  letI : Nonempty Space := ⟨marks true⟩
  exact ((kuratowskiEmbedding.isometry Space).isometryEquivOnRange.continuous).comp continuous

theorem originalJointCompactPathLaw_continuousSample_regular
    {Outcome : Type*} [MeasurableSpace Outcome]
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    OriginalJointUsualTestRegular (originalJointCompactPathLaw marks masses
      (continuousCadlagProbabilityCompletion law sample continuous evaluations)) := by
  have measurable := (originalJointCompactPathEncoding_continuous marks masses).measurable.comp
    (continuousCadlagSample_measurable_completion sample continuous evaluations)
  have regular := originalJointContinuousSampleLaw_regular law
    (fun outcome => OriginalJointCompactRepresentative.ofCompactSpace marks masses
      (continuousCadlagSampleCompletion sample continuous outcome)) measurable
    (fun outcome => originalJointCompactRepresentative_ofCompactSpace_continuous marks masses _
      (continuous outcome))
  convert regular using 1
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure Outcome).map
    (continuousCadlagSampleCompletion sample continuous)).map
    (originalJointCompactPathEncoding marks masses) = _
  rw [Measure.map_map (originalJointCompactPathEncoding_continuous marks masses).measurable
    (continuousCadlagSample_measurable_completion sample continuous evaluations)]
  rfl

theorem originalJointCompactPathLaw_spatial_continuousSample_regular
    {Outcome : Type*} [MeasurableSpace Outcome]
    {First : Type*} [MetricSpace First] [CompactSpace First] [MeasurableSpace First] [BorelSpace First]
    {Space : Type} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → First)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (spatial : First → Space) (spatialContinuous : Continuous spatial) :
    OriginalJointUsualTestRegular (originalJointCompactPathLaw marks masses
      ((continuousCadlagProbabilityCompletion law sample continuous evaluations).map
        (skorokhodCadlagContinuousCarrierMap_continuous_completion spatial spatialContinuous).measurable.aemeasurable)) := by
  rw [continuousCadlagProbability_spatial_map]
  exact originalJointCompactPathLaw_continuousSample_regular marks masses law _ _ _

end
end IGSIII34.Diffusion

