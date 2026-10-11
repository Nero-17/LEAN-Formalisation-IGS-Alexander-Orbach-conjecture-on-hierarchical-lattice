import IGSIII34.Diffusion.NormalizedAnchoredResolventCompletion20261011
import IGSIII34.Spectral.CoerciveFormHilbertCompletion20261011
import IGSIII34.Spectral.FormEigenbasisCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace IGSIII34.Diffusion

variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

theorem coercive_bilinear_unique_completion20261011
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

theorem parameterAnchoredResolventBilinear_symmetric_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (parameter : ℝ) (first second : Energy) :
    parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter first second =
      parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter second first := by
  rw [parameterAnchoredResolventBilinear_apply_completion20261011,
    parameterAnchoredResolventBilinear_apply_completion20261011, real_inner_comm first second,
    real_inner_comm (embedding first) (embedding second), mul_comm (anchorEvaluation first)]

def parameterEnergySolutionCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) : L2 →L[ℝ] Energy :=
  (parameterAnchoredResolventBilinear_coercive_completion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embedding.adjoint

theorem parameterEnergySolution_variational_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : L2) (test : Energy) :
    parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
      (parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne forcing) test =
        inner ℝ forcing (embedding test) := by
  let coercive := parameterAnchoredResolventBilinear_coercive_completion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne
  change parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
    (coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)) test = _
  rw [← coercive.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem parameterEnergySolution_eigenvalue_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (vector : L2) (eigenvalue : ℝ) (eigenvaluePositive : 0 < eigenvalue)
    (eigenvector : anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive vector = eigenvalue • vector) :
    parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne vector =
      (1 + (parameter - 1) * eigenvalue)⁻¹ •
        baseCoercive.continuousLinearEquivOfBilin.symm (embedding.adjoint vector) := by
  let solution := baseCoercive.continuousLinearEquivOfBilin.symm (embedding.adjoint vector)
  have image : embedding solution = eigenvalue • vector := eigenvector
  have denominatorPositive : 0 < 1 + (parameter - 1) * eigenvalue := by
    have := mul_nonneg (sub_nonneg.mpr parameterAtLeastOne) eigenvaluePositive.le
    linarith
  apply coercive_bilinear_unique_completion20261011 _
    (parameterAnchoredResolventBilinear_coercive_completion20261011 embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne)
  intro test
  rw [parameterEnergySolution_variational_completion20261011]
  have base := anchoredL2Resolvent_variational_completion20261011 embedding anchorEvaluation baseCoercive vector test
  have unscaled : parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter solution test =
      (1 + (parameter - 1) * eigenvalue) * inner ℝ vector (embedding test) := by
    rw [parameterAnchoredResolventBilinear_apply_completion20261011]
    rw [anchoredResolventBilinear_apply_completion20261011] at base
    change inner ℝ solution test - anchorEvaluation solution * anchorEvaluation test +
      inner ℝ (embedding solution) (embedding test) = inner ℝ vector (embedding test) at base
    rw [image, inner_smul_left] at base ⊢
    simp only [starRingEnd_apply, star_trivial] at base ⊢
    nlinarith [base]
  rw [map_smul, smul_apply, smul_eq_mul, unscaled, ← mul_assoc,
    inv_mul_cancel₀ denominatorPositive.ne', one_mul]

theorem parameterL2Solution_eigenvalue_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (vector : L2) (eigenvalue : ℝ) (eigenvaluePositive : 0 < eigenvalue)
    (eigenvector : anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive vector = eigenvalue • vector) :
    embedding (parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne vector) =
      (eigenvalue / (1 + (parameter - 1) * eigenvalue)) • vector := by
  rw [parameterEnergySolution_eigenvalue_completion20261011 _ _ _ _ _ _ _ eigenvaluePositive eigenvector, map_smul]
  change (1 + (parameter - 1) * eigenvalue)⁻¹ •
    anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive vector = _
  rw [eigenvector, smul_smul]
  congr 1
  ring

end
end IGSIII34.Spectral
