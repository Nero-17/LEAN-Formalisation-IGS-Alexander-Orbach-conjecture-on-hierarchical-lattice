import IGSIII34.Diffusion.OriginalJointCompactPathLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter TopologicalSpace

theorem jointMeasuredMarkedStateMap_fullState_surjective
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last] [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (continuous : Continuous mapping)
    (surjective : Function.Surjective mapping)
    (marks : Bool → First) (masses : Bool → ProbabilityMeasure First) :
    jointMeasuredMarkedStateMap mapping continuous (originalJointCompactFullState marks masses) =
      originalJointCompactFullState (mapping ∘ marks)
        (fun side => (masses side).map continuous.measurable.aemeasurable) := by
  apply Prod.ext
  · apply NonemptyCompacts.ext
    change mapping '' Set.univ = Set.univ
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr surjective
  · rfl

/-- Onto spatial isometries preserve the original joint class, including
the full geometric carrier and both physical probability masses. -/
theorem originalJointCompactPathEncoding_isometricTransport
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last] [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (isometry : Isometry mapping)
    (surjective : Function.Surjective mapping)
    (marks : Bool → First) (masses : Bool → ProbabilityMeasure First)
    (path : SkorokhodCadlagPathCompletion20261011 First) :
    originalJointCompactPathEncoding (mapping ∘ marks)
      (fun side => (masses side).map isometry.continuous.measurable.aemeasurable)
      (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous path) =
      originalJointCompactPathEncoding marks masses path := by
  apply originalJointCompactSpaceToExtended_isometry.injective
  rw [originalJointCompactPathEncoding_toExtended, originalJointCompactPathEncoding_toExtended,
    ← jointMeasuredMarkedStateMap_fullState_surjective mapping isometry.continuous surjective]
  exact extendedJointStatePathClass_isometricTransport mapping isometry
    (originalJointCompactFullState marks masses) path

theorem originalJointCompactPathLaw_isometricTransport
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last] [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (isometry : Isometry mapping)
    (surjective : Function.Surjective mapping)
    (marks : Bool → First) (masses : Bool → ProbabilityMeasure First)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 First)) :
    originalJointCompactPathLaw (mapping ∘ marks)
      (fun side => (masses side).map isometry.continuous.measurable.aemeasurable)
      (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        mapping isometry.continuous).measurable.aemeasurable) =
      originalJointCompactPathLaw marks masses law := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure _).map
      (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous)).map
      (originalJointCompactPathEncoding (mapping ∘ marks)
        (fun side => (masses side).map isometry.continuous.measurable.aemeasurable)) =
    (law : Measure _).map (originalJointCompactPathEncoding marks masses)
  rw [Measure.map_map
    (originalJointCompactPathEncoding_continuous (mapping ∘ marks)
      (fun side => (masses side).map isometry.continuous.measurable.aemeasurable)).measurable
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
      mapping isometry.continuous).measurable]
  apply Measure.map_congr
  exact Eventually.of_forall
    (originalJointCompactPathEncoding_isometricTransport mapping isometry surjective marks masses)

end
end IGSIII34.Diffusion
