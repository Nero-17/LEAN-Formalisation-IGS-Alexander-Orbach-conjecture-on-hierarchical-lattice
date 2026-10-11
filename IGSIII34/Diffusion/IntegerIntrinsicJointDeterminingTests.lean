import IGSIII34.Diffusion.OriginalJointCompactEmbedding
import IGSIII34.Diffusion.ExtendedJointCompactPathLaw
import IGSIII34.Diffusion.IntegerIntrinsicJointGHPPathTest
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped _root_.Topology NNReal BoundedContinuousFunction

/-- Every bounded Lipschitz test on the original joint metric extends to
the comparison space, retaining its Lipschitz constant and original values. -/
theorem exists_extended_original_joint_bounded_lipschitz_test
    (test : OriginalJointCompactSpace →ᵇ ℝ) (constant : ℝ≥0)
    (lipschitz : LipschitzWith constant test) :
    ∃ extension : ExtendedJointCompactSpace →ᵇ ℝ,
      LipschitzWith constant extension ∧
      ∀ point, extension (originalJointCompactSpaceToExtended point) = test point := by
  classical
  let initial : ExtendedJointCompactSpace → ℝ :=
    Function.extend originalJointCompactSpaceToExtended test (fun _ => 0)
  have initial_eq (point : OriginalJointCompactSpace) :
      initial (originalJointCompactSpaceToExtended point) = test point := by
    exact originalJointCompactSpaceToExtended_isometry.injective.extend_apply _ _ _
  have initialLipschitz : LipschitzOnWith constant initial
      (Set.range originalJointCompactSpaceToExtended) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨first, rfl⟩ _ ⟨last, rfl⟩
    rw [initial_eq, initial_eq,
      originalJointCompactSpaceToExtended_isometry.dist_eq]
    exact lipschitz.dist_le_mul first last
  obtain ⟨extension, extensionLipschitz, equality⟩ := initialLipschitz.extend_real
  let clipped : ExtendedJointCompactSpace → ℝ :=
    fun point => max (-‖test‖) (min ‖test‖ (extension point))
  have clippedLipschitz : LipschitzWith constant clipped :=
    (extensionLipschitz.const_min ‖test‖).const_max (-‖test‖)
  have clippedNorm (point : ExtendedJointCompactSpace) : ‖clipped point‖ ≤ ‖test‖ := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith [norm_nonneg test]) (min_le_left _ _)
  let bounded : ExtendedJointCompactSpace →ᵇ ℝ :=
    { toFun := clipped
      continuous_toFun := clippedLipschitz.continuous
      map_bounded' := ⟨2 * ‖test‖, fun first last => by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (by linarith [clippedNorm first, clippedNorm last])⟩ }
  refine ⟨bounded, clippedLipschitz, ?_⟩
  intro point
  have extensionEq : extension (originalJointCompactSpaceToExtended point) = test point :=
    (equality ⟨point, rfl⟩).symm.trans (initial_eq point)
  change max (-‖test‖) (min ‖test‖ (extension _)) = _
  rw [extensionEq]
  have bound := test.norm_coe_le_norm point
  rw [Real.norm_eq_abs, abs_le] at bound
  rw [min_eq_right bound.2, max_eq_right bound.1]

/-- Bounded Lipschitz tests of the genuine joint comparison metric are
intrinsic tests, including all spatial data and the entire cadlag path. -/
def IntegerIntrinsicJointGHPPathTest.ofExtendedBoundedLipschitz
    (test : ExtendedJointCompactSpace →ᵇ ℝ) (constant : ℝ≥0)
    (lipschitz : LipschitzWith constant test) : IntegerIntrinsicJointGHPPathTest where
  bound := ‖test‖₊
  spatialLipschitz := constant
  value Space _ _ _ _ state := test.compContinuous
    ⟨extendedJointStatePathClass state, (extendedJointStatePathClass_lipschitz state).continuous⟩
  bounded Space _ _ _ _ state := by
    exact test.norm_compContinuous_le _
  spatialStability Space _ _ _ _ first last path := by
    change |test (extendedJointStatePathClass first path) -
      test (extendedJointStatePathClass last path)| ≤ _
    have bound := lipschitz.dist_le_mul
      (extendedJointStatePathClass first path) (extendedJointStatePathClass last path)
    apply (show |test (extendedJointStatePathClass first path) -
      test (extendedJointStatePathClass last path)| ≤ constant *
        dist (extendedJointStatePathClass first path) (extendedJointStatePathClass last path)
      from bound).trans
    apply mul_le_mul_of_nonneg_left _ constant.coe_nonneg
    exact (extendedJointCompactDistance_le_cost
      (ExtendedJointCompactCoupling.sameCompactSpace first last path path)).trans_eq
      (ExtendedJointCompactCoupling.sameCompactSpace_same_path_cost first last path)
  isometricTransport First Last _ _ _ _ _ _ _ _ mapping isometry state path := by
    change test (extendedJointStatePathClass
      (jointMeasuredMarkedStateMap mapping isometry.continuous state)
      (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous path)) = _
    rw [extendedJointStatePathClass_isometricTransport mapping isometry state path]
    rfl

end
end IGSIII34.Diffusion
