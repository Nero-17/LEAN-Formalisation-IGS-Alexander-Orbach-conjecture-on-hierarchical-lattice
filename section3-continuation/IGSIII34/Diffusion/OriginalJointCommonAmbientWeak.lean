import IGSIII34.Diffusion.OriginalJointCompactPathLaw
import IGSIII34.Diffusion.IntegerIntrinsicJointDeterminingTests
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal BoundedContinuousFunction

/-- A common ambient controls the entire joint law. Its equality with
the original push-forward laws is an exact transport identity; no joint
weak convergence is assumed in this statement. -/
theorem originalJointCompactLaws_weak_of_common_ambient
    {Ambient : Type} [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (originalLaws : ℕ → ProbabilityMeasure OriginalJointCompactSpace)
    (originalLaw : ProbabilityMeasure OriginalJointCompactSpace)
    (states : ℕ → JointMeasuredMarkedState Ambient) (state : JointMeasuredMarkedState Ambient)
    (pathLaws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Ambient))
    (pathLaw : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Ambient))
    (placedFinite : ∀ index, (originalLaws index).map
      originalJointCompactSpaceToExtended_isometry.continuous.measurable.aemeasurable =
        extendedJointCompactPathLaw (states index) (pathLaws index))
    (placedLimit : originalLaw.map
      originalJointCompactSpaceToExtended_isometry.continuous.measurable.aemeasurable =
        extendedJointCompactPathLaw state pathLaw)
    (spatial : Tendsto (fun index => jointMeasuredMarkedStateCost (states index) state) atTop (𝓝 0))
    (paths : Tendsto pathLaws atTop (𝓝 pathLaw)) :
    Tendsto originalLaws atTop (𝓝 originalLaw) := by
  apply ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro function bounded lipschitz
  obtain ⟨constant, lipschitz⟩ := lipschitz
  let test : OriginalJointCompactSpace →ᵇ ℝ := {
    toFun := function
    continuous_toFun := lipschitz.continuous
    map_bounded' := bounded }
  obtain ⟨extension, extensionLipschitz, extensionIdentity⟩ :=
    exists_extended_original_joint_bounded_lipschitz_test test constant lipschitz
  let intrinsic := IntegerIntrinsicJointGHPPathTest.ofExtendedBoundedLipschitz
    extension constant extensionLipschitz
  have response := integer_intrinsic_joint_test_response_tendsto intrinsic
    states state pathLaws pathLaw spatial paths
  have identity
      (jointLaw : ProbabilityMeasure OriginalJointCompactSpace)
      (placedState : JointMeasuredMarkedState Ambient)
      (placedPathLaw : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Ambient))
      (placement : jointLaw.map
        originalJointCompactSpaceToExtended_isometry.continuous.measurable.aemeasurable =
          extendedJointCompactPathLaw placedState placedPathLaw) :
      (∫ point, function point ∂(jointLaw : Measure _)) =
        ∫ path, intrinsic.value Ambient placedState path ∂(placedPathLaw : Measure _) := by
    have mapped : (∫ point, extension point ∂(jointLaw.map
        originalJointCompactSpaceToExtended_isometry.continuous.measurable.aemeasurable : Measure _)) =
        ∫ point, function point ∂(jointLaw : Measure _) := by
      rw [ProbabilityMeasure.toMeasure_map,
        integral_map originalJointCompactSpaceToExtended_isometry.continuous.measurable.aemeasurable
          extension.continuous.aestronglyMeasurable]
      apply integral_congr_ae
      exact Eventually.of_forall extensionIdentity
    rw [placement, extendedJointCompactPathLaw_integral] at mapped
    exact mapped.symm
  have finiteIdentity := funext (fun index => identity (originalLaws index)
    (states index) (pathLaws index) (placedFinite index))
  rw [finiteIdentity, identity originalLaw state pathLaw placedLimit]
  exact response

/-- Original compact carriers, their two physical masses and planted
marks may vary with the index. True isometric placement in one compact
ambient, spatial joint convergence and whole-cadlag weak convergence
imply weak convergence of their genuine original joint laws. -/
theorem originalJointCompactPathLaws_weak_of_isometric_common_ambient
    (Sources : ℕ → Type) [∀ index, MetricSpace (Sources index)]
    [∀ index, CompactSpace (Sources index)] [∀ index, MeasurableSpace (Sources index)]
    [∀ index, BorelSpace (Sources index)]
    {Target Ambient : Type} [MetricSpace Target] [CompactSpace Target]
    [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (sourceMarks : ∀ index, Bool → Sources index)
    (sourceMasses : ∀ index, Bool → ProbabilityMeasure (Sources index))
    (targetMarks : Bool → Target) (targetMasses : Bool → ProbabilityMeasure Target)
    (sourceLaws : ∀ index, ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 (Sources index)))
    (targetLaw : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Target))
    (sources : ∀ index, Sources index → Ambient) (sourceIsometry : ∀ index, Isometry (sources index))
    (target : Target → Ambient) (targetIsometry : Isometry target)
    (spatial : Tendsto (fun index => jointMeasuredMarkedStateCost
      (jointMeasuredMarkedStateMap (sources index) (sourceIsometry index).continuous
        (originalJointCompactFullState (sourceMarks index) (sourceMasses index)))
      (jointMeasuredMarkedStateMap target targetIsometry.continuous
        (originalJointCompactFullState targetMarks targetMasses))) atTop (𝓝 0))
    (paths : Tendsto (fun index => (sourceLaws index).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (sources index) (sourceIsometry index).continuous).measurable.aemeasurable) atTop
      (𝓝 (targetLaw.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        target targetIsometry.continuous).measurable.aemeasurable))) :
    Tendsto (fun index => originalJointCompactPathLaw (sourceMarks index) (sourceMasses index)
      (sourceLaws index)) atTop
      (𝓝 (originalJointCompactPathLaw targetMarks targetMasses targetLaw)) := by
  apply originalJointCompactLaws_weak_of_common_ambient
    (fun index => originalJointCompactPathLaw (sourceMarks index) (sourceMasses index) (sourceLaws index))
    (originalJointCompactPathLaw targetMarks targetMasses targetLaw)
    (fun index => jointMeasuredMarkedStateMap (sources index) (sourceIsometry index).continuous
      (originalJointCompactFullState (sourceMarks index) (sourceMasses index)))
    (jointMeasuredMarkedStateMap target targetIsometry.continuous
      (originalJointCompactFullState targetMarks targetMasses))
    (fun index => (sourceLaws index).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (sources index) (sourceIsometry index).continuous).measurable.aemeasurable)
    (targetLaw.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
      target targetIsometry.continuous).measurable.aemeasurable)
  · intro index
    rw [originalJointCompactPathLaw_toExtended,
      extendedJointCompactPathLaw_isometricTransport]
  · rw [originalJointCompactPathLaw_toExtended,
      extendedJointCompactPathLaw_isometricTransport]
  · exact spatial
  · exact paths

end
end IGSIII34.Diffusion
