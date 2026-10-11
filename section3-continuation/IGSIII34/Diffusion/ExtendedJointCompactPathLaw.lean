import IGSIII34.Diffusion.ExtendedJointCompactDistance
import IGSIII34.Diffusion.ExtendedJointCompactPlacement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal

def extendedJointStatePathClass
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space) : ExtendedJointCompactSpace :=
  extendedJointCompactClass (.ofCompactSpace state path)

theorem extendedJointStatePathClass_lipschitz
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space) :
    LipschitzWith 1 (extendedJointStatePathClass state) := by
  apply LipschitzWith.of_dist_le_mul
  intro first last
  change extendedJointCompactDistance (.ofCompactSpace state first)
    (.ofCompactSpace state last) ≤ (1 : ℝ≥0) * dist first last
  simpa only [NNReal.coe_one, one_mul] using
    (extendedJointCompactDistance_le_cost
      (ExtendedJointCompactCoupling.sameCompactSpace state state first last)).trans_eq
        (ExtendedJointCompactCoupling.sameCompactSpace_same_state_cost state first last)

theorem extendedJointStatePathClass_isometricTransport
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last]
    [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (isometry : Isometry mapping)
    (state : JointMeasuredMarkedState First)
    (path : SkorokhodCadlagPathCompletion20261011 First) :
    extendedJointStatePathClass (jointMeasuredMarkedStateMap mapping isometry.continuous state)
      (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous path) =
      extendedJointStatePathClass state path := by
  apply Eq.symm
  apply dist_le_zero.mp
  exact (extendedJointCompactDistance_le_cost
    (ExtendedJointCompactCoupling.isometricTransport mapping isometry state path)).trans_eq
      (ExtendedJointCompactCoupling.isometricTransport_cost mapping isometry state path)

def extendedJointCompactPathLaw
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space)) :
    ProbabilityMeasure ExtendedJointCompactSpace :=
  law.map (extendedJointStatePathClass_lipschitz state).continuous.measurable.aemeasurable

theorem extendedJointCompactPathLaw_integral
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (test : ExtendedJointCompactSpace →ᵇ ℝ) :
    (∫ point, test point ∂(extendedJointCompactPathLaw state law : Measure _)) =
      ∫ path, test (extendedJointStatePathClass state path) ∂(law : Measure _) := by
  exact integral_map (extendedJointStatePathClass_lipschitz state).continuous.measurable.aemeasurable
    test.continuous.aestronglyMeasurable

theorem extendedJointCompactPathLaw_tendsto
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space)
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (weak : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => extendedJointCompactPathLaw state (laws index)) atTop
      (𝓝 (extendedJointCompactPathLaw state law)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law weak
    (extendedJointStatePathClass_lipschitz state).continuous

theorem extendedJointCompactPathLaw_isometricTransport
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last]
    [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (isometry : Isometry mapping)
    (state : JointMeasuredMarkedState First)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 First)) :
    extendedJointCompactPathLaw (jointMeasuredMarkedStateMap mapping isometry.continuous state)
      (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        mapping isometry.continuous).measurable.aemeasurable) =
      extendedJointCompactPathLaw state law := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure _).map
      (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous)).map
      (extendedJointStatePathClass (jointMeasuredMarkedStateMap mapping isometry.continuous state)) =
    (law : Measure _).map (extendedJointStatePathClass state)
  rw [Measure.map_map
    (extendedJointStatePathClass_lipschitz
      (jointMeasuredMarkedStateMap mapping isometry.continuous state)).continuous.measurable
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
      mapping isometry.continuous).measurable]
  apply Measure.map_congr
  exact Eventually.of_forall (extendedJointStatePathClass_isometricTransport mapping isometry state)

end
end IGSIII34.Diffusion
