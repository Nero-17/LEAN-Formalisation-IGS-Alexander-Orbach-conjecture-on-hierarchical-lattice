import IGSIII34.Diffusion.SpatialLevyProkhorovIsometry
import IGSIII34.Diffusion.IntrinsicJointGHPPathTest

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BigOperators

/-- The entire true Hausdorff/ordered-mark/both-mass state cost is
preserved exactly by a spatial isometry; no changed coding metric enters. -/
theorem jointMeasuredMarkedStateCost_isometric_map
    {Source Target : Type*} [MetricSpace Source] [CompactSpace Source]
    [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (mapping : Source → Target) (isometry : Isometry mapping)
    (first second : JointMeasuredMarkedState Source) :
    jointMeasuredMarkedStateCost
      (jointMeasuredMarkedStateMap mapping isometry.continuous first)
      (jointMeasuredMarkedStateMap mapping isometry.continuous second) =
      jointMeasuredMarkedStateCost first second := by
  unfold jointMeasuredMarkedStateCost
  congr 1
  · congr 1
    · rw [Metric.NonemptyCompacts.dist_eq, Metric.NonemptyCompacts.dist_eq]
      change Metric.hausdorffDist (mapping '' (first.1 : Set Source)) (mapping '' (second.1 : Set Source)) =
        Metric.hausdorffDist (first.1 : Set Source) (second.1 : Set Source)
      exact Metric.hausdorffDist_image isometry
    · apply Finset.sum_congr rfl
      intro side _
      exact isometry.dist_eq _ _
  · apply Finset.sum_congr rfl
    intro counting _
    exact probability_levyProkhorovDist_map_spatial_isometry _ _ mapping isometry

end
end IGSIII34.Diffusion

#print axioms IGSIII34.Diffusion.jointMeasuredMarkedStateCost_isometric_map
