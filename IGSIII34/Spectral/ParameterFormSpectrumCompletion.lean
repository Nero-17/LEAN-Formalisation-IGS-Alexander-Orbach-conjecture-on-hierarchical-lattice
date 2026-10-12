import IGSIII34.Diffusion.NormalizedAnchoredResolventCompletion
import IGSIII34.Spectral.CoerciveFormHilbertCompletion
import IGSIII34.Spectral.FormEigenbasisCompletion

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace IGSIII34.Diffusion

variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

theorem coercive_bilinear_unique_completion
    (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ) (coercive : IsCoercive bilinear)
    (first second : Energy) (equal : ∀ test, bilinear first test = bilinear second test) :
    first = second := by
  apply coercive.continuousLinearEquivOfBilin.injective
  apply (toDual ℝ Energy).injective
  ext test
  rw [toDual_apply_apply, toDual_apply_apply,
    coercive.continuousLinearEquivOfBilin_apply,
    coercive.continuousLinearEquivOfBilin_apply]
  exact equal test

theorem parameterAnchoredResolventBilinear_symmetric_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (parameter : ℝ) (first second : Energy) :
    parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter first second =
      parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter second first := by
  rw [parameterAnchoredResolventBilinear_apply_completion,
    parameterAnchoredResolventBilinear_apply_completion, real_inner_comm first second,
    real_inner_comm (embedding first) (embedding second), mul_comm (anchorEvaluation first)]

def parameterEnergySolutionCompletion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) : L2 →L[ℝ] Energy :=
  (parameterAnchoredResolventBilinear_coercive_completion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embedding.adjoint

theorem parameterEnergySolution_variational_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : L2) (test : Energy) :
    parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter
      (parameterEnergySolutionCompletion embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne forcing) test =
        inner ℝ forcing (embedding test) := by
  let coercive := parameterAnchoredResolventBilinear_coercive_completion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne
  change parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter
    (coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)) test = _
  rw [← coercive.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem parameterEnergySolution_eigenvalue_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (vector : L2) (eigenvalue : ℝ) (eigenvaluePositive : 0 < eigenvalue)
    (eigenvector : anchoredL2ResolventCompletion embedding anchorEvaluation baseCoercive vector = eigenvalue • vector) :
    parameterEnergySolutionCompletion embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne vector =
      (1 + (parameter - 1) * eigenvalue)⁻¹ •
        baseCoercive.continuousLinearEquivOfBilin.symm (embedding.adjoint vector) := by
  let solution := baseCoercive.continuousLinearEquivOfBilin.symm (embedding.adjoint vector)
  have image : embedding solution = eigenvalue • vector := eigenvector
  have denominatorPositive : 0 < 1 + (parameter - 1) * eigenvalue := by
    have := mul_nonneg (sub_nonneg.mpr parameterAtLeastOne) eigenvaluePositive.le
    linarith
  apply coercive_bilinear_unique_completion _
    (parameterAnchoredResolventBilinear_coercive_completion embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne)
  intro test
  rw [parameterEnergySolution_variational_completion]
  have base := anchoredL2Resolvent_variational_completion embedding anchorEvaluation baseCoercive vector test
  have unscaled : parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter solution test =
      (1 + (parameter - 1) * eigenvalue) * inner ℝ vector (embedding test) := by
    rw [parameterAnchoredResolventBilinear_apply_completion]
    rw [anchoredResolventBilinear_apply_completion] at base
    change inner ℝ solution test - anchorEvaluation solution * anchorEvaluation test +
      inner ℝ (embedding solution) (embedding test) = inner ℝ vector (embedding test) at base
    rw [image, inner_smul_left] at base ⊢
    simp only [starRingEnd_apply, star_trivial] at base ⊢
    nlinarith [base]
  rw [map_smul, smul_apply, smul_eq_mul, unscaled, ← mul_assoc,
    inv_mul_cancel₀ denominatorPositive.ne', one_mul]

theorem parameterL2Solution_eigenvalue_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (vector : L2) (eigenvalue : ℝ) (eigenvaluePositive : 0 < eigenvalue)
    (eigenvector : anchoredL2ResolventCompletion embedding anchorEvaluation baseCoercive vector = eigenvalue • vector) :
    embedding (parameterEnergySolutionCompletion embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne vector) =
      (eigenvalue / (1 + (parameter - 1) * eigenvalue)) • vector := by
  rw [parameterEnergySolution_eigenvalue_completion _ _ _ _ _ _ _ eigenvaluePositive eigenvector, map_smul]
  change (1 + (parameter - 1) * eigenvalue)⁻¹ •
    anchoredL2ResolventCompletion embedding anchorEvaluation baseCoercive vector = _
  rw [eigenvector, smul_smul]
  congr 1
  ring

end
end IGSIII34.Spectral
