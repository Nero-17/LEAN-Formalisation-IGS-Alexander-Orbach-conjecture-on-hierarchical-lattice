import IGSIII34.Diffusion.OriginalJointCompactPathEncodingContinuous
import IGSIII34.Diffusion.OriginalExtendedJointCompactPathBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped Topology BoundedContinuousFunction

def originalJointCompactPathLaw
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space)) :
    ProbabilityMeasure OriginalJointCompactSpace :=
  law.map (originalJointCompactPathEncoding_continuous marks masses).measurable.aemeasurable

theorem originalJointCompactPathLaw_integral
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (test : OriginalJointCompactSpace →ᵇ ℝ) :
    (∫ point, test point ∂(originalJointCompactPathLaw marks masses law : Measure _)) =
      ∫ path, test (originalJointCompactPathEncoding marks masses path) ∂(law : Measure _) := by
  exact integral_map (originalJointCompactPathEncoding_continuous marks masses).measurable.aemeasurable
    test.continuous.aestronglyMeasurable

theorem originalJointCompactPathLaw_tendsto
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (weak : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => originalJointCompactPathLaw marks masses (laws index)) atTop
      (𝓝 (originalJointCompactPathLaw marks masses law)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law weak
    (originalJointCompactPathEncoding_continuous marks masses)

theorem originalJointCompactPathLaw_toExtended
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space)) :
    (originalJointCompactPathLaw marks masses law).map
        originalJointCompactSpaceToExtended_isometry.continuous.measurable.aemeasurable =
      extendedJointCompactPathLaw (originalJointCompactFullState marks masses) law := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure _).map (originalJointCompactPathEncoding marks masses)).map
      originalJointCompactSpaceToExtended =
    (law : Measure _).map (extendedJointStatePathClass (originalJointCompactFullState marks masses))
  rw [Measure.map_map originalJointCompactSpaceToExtended_isometry.continuous.measurable
    (originalJointCompactPathEncoding_continuous marks masses).measurable]
  apply Measure.map_congr
  exact Eventually.of_forall (originalJointCompactPathEncoding_toExtended marks masses)

end
end IGSIII34.Diffusion
