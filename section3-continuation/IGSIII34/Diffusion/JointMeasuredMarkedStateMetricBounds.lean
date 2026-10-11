import IGSIII34.Diffusion.IntrinsicJointGHPPathTest
import IGSIII.Geometry.ExceptionalTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BigOperators

theorem jointMeasuredMarkedStateCost_triangle
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (first middle last : JointMeasuredMarkedState Space) :
    jointMeasuredMarkedStateCost first last ≤
      jointMeasuredMarkedStateCost first middle + jointMeasuredMarkedStateCost middle last := by
  unfold jointMeasuredMarkedStateCost
  have carrier := dist_triangle first.1 middle.1 last.1
  have marks := Finset.sum_le_sum (s := Finset.univ) (fun side _ =>
    dist_triangle (first.2.1 side) (middle.2.1 side) (last.2.1 side))
  have masses := Finset.sum_le_sum (s := Finset.univ) (fun side _ =>
    levyProkhorovDist_triangle (first.2.2 side : Measure Space)
      (middle.2.2 side : Measure Space) (last.2.2 side : Measure Space))
  simp only [Finset.sum_add_distrib] at marks masses
  linarith

theorem jointMeasuredMarkedStateCost_isometric_map_le
    {First Last : Type*} [MetricSpace First] [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (isometry : Isometry mapping)
    (first last : JointMeasuredMarkedState First) :
    jointMeasuredMarkedStateCost (jointMeasuredMarkedStateMap mapping isometry.continuous first)
      (jointMeasuredMarkedStateMap mapping isometry.continuous last) ≤
    jointMeasuredMarkedStateCost first last := by
  have carrier : dist (first.1.map mapping isometry.continuous)
      (last.1.map mapping isometry.continuous) = dist first.1 last.1 := by
    rw [Metric.NonemptyCompacts.dist_eq, Metric.NonemptyCompacts.dist_eq,
      NonemptyCompacts.coe_map, NonemptyCompacts.coe_map]
    exact Metric.hausdorffDist_image isometry
  have masses (side : Bool) : levyProkhorovDist
      ((first.2.2 side).map isometry.continuous.measurable.aemeasurable : Measure Last)
      ((last.2.2 side).map isometry.continuous.measurable.aemeasurable : Measure Last) ≤
      levyProkhorovDist (first.2.2 side : Measure First) (last.2.2 side : Measure First) := by
    apply ENNReal.toReal_mono (levyProkhorovEDist_ne_top _ _)
    exact IGSIII.Geometry.levyProkhorovEDist_map_le_of_lipschitz_one _ _ mapping isometry.lipschitz
  unfold jointMeasuredMarkedStateCost jointMeasuredMarkedStateMap
  dsimp only
  rw [carrier]
  simp only [Function.comp_apply, isometry.dist_eq]
  exact add_le_add le_rfl (Finset.sum_le_sum (fun side _ => masses side))

theorem jointMeasuredMarkedStateMap_comp
    {First Middle Last : Type*}
    [MetricSpace First] [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Middle] [MeasurableSpace Middle] [BorelSpace Middle]
    [MetricSpace Last] [MeasurableSpace Last] [BorelSpace Last]
    (firstMapping : First → Middle) (firstContinuous : Continuous firstMapping)
    (lastMapping : Middle → Last) (lastContinuous : Continuous lastMapping)
    (state : JointMeasuredMarkedState First) :
    jointMeasuredMarkedStateMap lastMapping lastContinuous
      (jointMeasuredMarkedStateMap firstMapping firstContinuous state) =
    jointMeasuredMarkedStateMap (lastMapping ∘ firstMapping)
      (lastContinuous.comp firstContinuous) state := by
  apply Prod.ext
  · apply NonemptyCompacts.ext
    simp only [jointMeasuredMarkedStateMap, NonemptyCompacts.coe_map, Set.image_image]
    rfl
  · apply Prod.ext
    · rfl
    · funext side
      apply ProbabilityMeasure.toMeasure_injective
      exact Measure.map_map lastContinuous.measurable firstContinuous.measurable

end
end IGSIII34.Diffusion
