import IGSIII.Geometry.ExceptionalTransport
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Metric Set

/-- An actual isometric embedding of a compact spatial carrier preserves
the full Levy-Prokhorov edistance of arbitrary Borel measures exactly. -/
theorem levyProkhorovEDist_map_spatial_isometry
    {Source Target : Type*} [MetricSpace Source] [CompactSpace Source]
    [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (first second : Measure Source) (mapping : Source → Target) (isometry : Isometry mapping) :
    levyProkhorovEDist (first.map mapping) (second.map mapping) = levyProkhorovEDist first second := by
  have measurable := isometry.continuous.measurable
  have embedding := isometry.isClosedEmbedding.measurableEmbedding
  have preimageThickening (radius : ℝ) (event : Set Source) :
      mapping ⁻¹' Metric.thickening radius (mapping '' event) = Metric.thickening radius event := by
    ext point
    constructor
    · intro member
      obtain ⟨nearby, ⟨original, originalMember, rfl⟩, close⟩ := Metric.mem_thickening_iff.mp member
      apply Metric.mem_thickening_iff.mpr
      rw [isometry.dist_eq] at close
      exact ⟨original, originalMember, close⟩
    · intro member
      obtain ⟨nearby, nearbyMember, close⟩ := Metric.mem_thickening_iff.mp member
      apply Metric.mem_thickening_iff.mpr
      refine ⟨mapping nearby, Set.mem_image_of_mem mapping nearbyMember, ?_⟩
      rw [isometry.dist_eq]
      exact close
  refine le_antisymm (IGSIII.Geometry.levyProkhorovEDist_map_le_of_lipschitz_one first second mapping isometry.lipschitz) ?_
  apply levyProkhorovEDist_le_of_forall
  intro epsilon event epsilonLarge epsilonFinite eventMeasurable
  have imageMeasurable := embedding.measurableSet_image.mpr eventMeasurable
  have left := left_measure_le_of_levyProkhorovEDist_lt epsilonLarge imageMeasurable
  have right := right_measure_le_of_levyProkhorovEDist_lt epsilonLarge imageMeasurable
  rw [Measure.map_apply measurable imageMeasurable,
    Measure.map_apply measurable Metric.isOpen_thickening.measurableSet,
    isometry.injective.preimage_image, preimageThickening] at left right
  exact ⟨left, right⟩

theorem levyProkhorovDist_map_spatial_isometry
    {Source Target : Type*} [MetricSpace Source] [CompactSpace Source]
    [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (first second : Measure Source) (mapping : Source → Target) (isometry : Isometry mapping) :
    levyProkhorovDist (first.map mapping) (second.map mapping) = levyProkhorovDist first second := by
  unfold levyProkhorovDist
  rw [levyProkhorovEDist_map_spatial_isometry first second mapping isometry]

theorem probability_levyProkhorovEDist_map_spatial_isometry
    {Source Target : Type*} [MetricSpace Source] [CompactSpace Source]
    [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (first second : ProbabilityMeasure Source) (mapping : Source → Target) (isometry : Isometry mapping) :
    levyProkhorovEDist (first.map isometry.continuous.measurable.aemeasurable : Measure Target)
      (second.map isometry.continuous.measurable.aemeasurable : Measure Target) =
      levyProkhorovEDist (first : Measure Source) (second : Measure Source) :=
  levyProkhorovEDist_map_spatial_isometry _ _ mapping isometry

theorem probability_levyProkhorovDist_map_spatial_isometry
    {Source Target : Type*} [MetricSpace Source] [CompactSpace Source]
    [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (first second : ProbabilityMeasure Source) (mapping : Source → Target) (isometry : Isometry mapping) :
    levyProkhorovDist (first.map isometry.continuous.measurable.aemeasurable : Measure Target)
      (second.map isometry.continuous.measurable.aemeasurable : Measure Target) =
      levyProkhorovDist (first : Measure Source) (second : Measure Source) :=
  levyProkhorovDist_map_spatial_isometry _ _ mapping isometry

end
end IGSIII34.Diffusion
