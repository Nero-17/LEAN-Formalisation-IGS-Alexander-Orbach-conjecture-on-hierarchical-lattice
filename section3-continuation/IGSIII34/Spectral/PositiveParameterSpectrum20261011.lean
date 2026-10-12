import IGSIII34.Spectral.ActualSpectralDataCompletion20261011

/-! Parameter-form spectral evaluation with explicit coercivity. The actual
positive-parameter corollary proves coercivity for every s > 0 using
min(1,s) times the energy-plus-L2 form; no resolvent identity is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral.PositiveParameter
noncomputable section
open InnerProductSpace IGSIII34.Diffusion IGSIII34.Spectral
variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

def parameterEnergySolutionCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterCoercive : IsCoercive (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter)) : L2 →L[ℝ] Energy :=
  (parameterCoercive).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embedding.adjoint

theorem parameterEnergySolution_variational_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterCoercive : IsCoercive (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter)) (forcing : L2) (test : Energy) :
    parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
      (parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive forcing) test =
        inner ℝ forcing (embedding test) := by
  let coercive := parameterCoercive
  change parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
    (coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)) test = _
  rw [← coercive.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem parameterEnergySolution_eigenvalue_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterCoercive : IsCoercive (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter))
    (vector : L2) (eigenvalue : ℝ) (eigenvaluePositive : 0 < eigenvalue)
    (denominatorPositive : 0 < 1 + (parameter - 1) * eigenvalue)
    (eigenvector : anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive vector = eigenvalue • vector) :
    parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive vector =
      (1 + (parameter - 1) * eigenvalue)⁻¹ •
        baseCoercive.continuousLinearEquivOfBilin.symm (embedding.adjoint vector) := by
  let solution := baseCoercive.continuousLinearEquivOfBilin.symm (embedding.adjoint vector)
  have image : embedding solution = eigenvalue • vector := eigenvector
  apply coercive_bilinear_unique_completion20261011 _
    (parameterCoercive)
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
    (parameter : ℝ) (parameterCoercive : IsCoercive (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter))
    (vector : L2) (eigenvalue : ℝ) (eigenvaluePositive : 0 < eigenvalue)
    (denominatorPositive : 0 < 1 + (parameter - 1) * eigenvalue)
    (eigenvector : anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive vector = eigenvalue • vector) :
    embedding (parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive vector) =
      (eigenvalue / (1 + (parameter - 1) * eigenvalue)) • vector := by
  rw [parameterEnergySolution_eigenvalue_completion20261011 _ _ _ _ _ _ _ eigenvaluePositive denominatorPositive eigenvector, map_smul]
  change (1 + (parameter - 1) * eigenvalue)⁻¹ •
    anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive vector = _
  rw [eigenvector, smul_smul]
  congr 1
  ring

end
end IGSIII34.Spectral.PositiveParameter
