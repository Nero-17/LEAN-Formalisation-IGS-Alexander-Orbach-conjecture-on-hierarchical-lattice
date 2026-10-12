import IGSIII34.Diffusion.IntrinsicJointGHPPathTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory
open scoped _root_.Topology NNReal

theorem intrinsic_joint_test_integral_bound
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (test : IntrinsicJointGHPPathTest) (state : JointMeasuredMarkedState Space)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Space)) :
    ‖∫ path, test.value Space state path ∂(law : Measure _)‖ ≤ test.bound :=
  ((test.value Space state).norm_integral_le_norm (law : Measure _)).trans (test.bounded Space state)

/-- A joint response is unchanged by the true isometric placement of the
entire physical measured and marked space and its entire path law. -/
theorem intrinsic_joint_test_integral_isometric_transport
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last] [MeasurableSpace Last] [BorelSpace Last]
    (test : IntrinsicJointGHPPathTest) (mapping : First → Last) (isometry : Isometry mapping)
    (state : JointMeasuredMarkedState First)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion First)) :
    (∫ path, test.value Last (jointMeasuredMarkedStateMap mapping isometry.continuous state) path
      ∂(law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion
        mapping isometry.continuous).measurable.aemeasurable : Measure _)) =
    ∫ path, test.value First state path ∂(law : Measure _) := by
  change (∫ path, test.value Last (jointMeasuredMarkedStateMap mapping isometry.continuous state) path
    ∂(law : Measure _).map (skorokhodCadlagContinuousCarrierMapCompletion mapping isometry.continuous)) = _
  rw [integral_map (skorokhodCadlagContinuousCarrierMap_continuous_completion
    mapping isometry.continuous).measurable.aemeasurable
    (test.value Last (jointMeasuredMarkedStateMap mapping isometry.continuous state)).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun path => test.isometricTransport First Last mapping isometry state path)

end
end IGSIII34.Diffusion
