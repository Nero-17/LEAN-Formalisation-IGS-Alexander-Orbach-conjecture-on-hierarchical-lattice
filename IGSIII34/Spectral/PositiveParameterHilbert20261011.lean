import IGSIII34.Spectral.PositiveParameterSpectrum20261011
import IGSIII34.Spectral.FormEigenvectorsImageCompletion20261011
import IGSIII34.Spectral.HilbertEvaluation
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral.PositiveParameter
noncomputable section
open InnerProductSpace IGSIII34.Diffusion IGSIII34.Spectral
variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]
  (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
  (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
  (parameter : ℝ) (parameterCoercive : IsCoercive (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter))

@[reducible] def parameterFormHilbertCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterCoercive : IsCoercive (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter)) : Type _ :=
  coerciveFormHilbertCompletion20261011
    (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter)
    (parameterAnchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation parameter)
    (parameterCoercive)

def parameterFormEquivCompletion20261011 :
    parameterFormHilbertCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive ≃L[ℝ] Energy :=
  coerciveFormEquivCompletion20261011
    (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter)
    (parameterAnchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation parameter)
    (parameterCoercive)

def parameterFormEmbeddingCompletion20261011 :
    parameterFormHilbertCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive →L[ℝ] L2 :=
  embedding.comp (parameterFormEquivCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive).toContinuousLinearMap

def parameterFormSolutionCompletion20261011 :
    L2 →L[ℝ] parameterFormHilbertCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive :=
  (parameterFormEquivCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive).symm.toContinuousLinearMap.comp
    (parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive)

theorem parameterFormSolution_variational_completion20261011
    (forcing : L2) (test : parameterFormHilbertCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive) :
    inner ℝ (parameterFormSolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive forcing) test =
      inner ℝ forcing (parameterFormEmbeddingCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive test) := by
  change parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
    (parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive forcing) test =
      inner ℝ forcing (embedding test)
  exact parameterEnergySolution_variational_completion20261011 _ _ _ _ _ _ _

theorem parameterFormEmbedding_injective_completion20261011 (injective : Function.Injective embedding) :
    Function.Injective (parameterFormEmbeddingCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive) :=
  injective.comp (parameterFormEquivCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive).injective

def parameterResolventEigenvaluesCompletion20261011 {Index : Type*} (eigenvalues : Index → ℝ) : Index → ℝ :=
  fun index => eigenvalues index / (1 + (parameter - 1) * eigenvalues index)

theorem parameterResolventEigenvalues_positive_completion20261011 {Index : Type*}
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (denominatorsPositive : ∀ index, 0 < 1 + (parameter - 1) * eigenvalues index) (index : Index) :
    0 < parameterResolventEigenvaluesCompletion20261011 parameter eigenvalues index := by
  apply div_pos (positive index)
  exact denominatorsPositive index

theorem parameterResolventEigenvalues_inverse_completion20261011 {Index : Type*}
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (denominatorsPositive : ∀ index, 0 < 1 + (parameter - 1) * eigenvalues index) (index : Index) :
    (parameterResolventEigenvaluesCompletion20261011 parameter eigenvalues index)⁻¹ =
      parameter + (eigenvalues index)⁻¹ - 1 := by
  dsimp [parameterResolventEigenvaluesCompletion20261011]
  rw [inv_div]
  field_simp [(positive index).ne']
  ring

def parameterFormHilbertBasisCompletion20261011 {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (denominatorsPositive : ∀ index, 0 < 1 + (parameter - 1) * eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive
      (basis index) = eigenvalues index • basis index) :
    HilbertBasis Index ℝ (parameterFormHilbertCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive) :=
  resolventEnergyHilbertBasisCompletion20261011
    (parameterFormEmbeddingCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive)
    (parameterFormEmbedding_injective_completion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive injective)
    (parameterFormSolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive)
    (parameterFormSolution_variational_completion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive)
    basis (parameterResolventEigenvaluesCompletion20261011 parameter eigenvalues)
    (parameterResolventEigenvalues_positive_completion20261011 parameter eigenvalues positive denominatorsPositive)
    (fun index => parameterL2Solution_eigenvalue_completion20261011 embedding anchorEvaluation baseCoercive
      parameter parameterCoercive (basis index) (eigenvalues index) (positive index) (denominatorsPositive index) (eigenvectors index))

def parameterFormEvaluationCompletion20261011 (evaluation : StrongDual ℝ Energy) :
    StrongDual ℝ (parameterFormHilbertCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive) :=
  evaluation.comp (parameterFormEquivCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive).toContinuousLinearMap

theorem parameterFormEvaluation_parseval_completion20261011 {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (denominatorsPositive : ∀ index, 0 < 1 + (parameter - 1) * eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive
      (basis index) = eigenvalues index • basis index)
    (evaluation : StrongDual ℝ Energy) :
    HasSum (fun index =>
      parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive evaluation
        (parameterFormHilbertBasisCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive
          injective basis eigenvalues positive denominatorsPositive eigenvectors index) ^ 2)
      (‖parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive evaluation‖ ^ 2) :=
  hilbert_basis_evaluation_parseval _ _

theorem parameterFormEvaluation_variational_completion20261011 (evaluation : StrongDual ℝ Energy) :
    sSup (Set.range (fun function : Energy => evaluation function ^ 2 /
      parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter function function)) =
      ‖parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive evaluation‖ ^ 2 := by
  have identity := evaluation_variational_identity
    (parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive evaluation)
  have rangeEquality : Set.range (fun function : Energy => evaluation function ^ 2 /
      parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter function function) =
      Set.range (fun function : parameterFormHilbertCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive =>
        parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive evaluation function ^ 2 / ‖function‖ ^ 2) := by
    ext result
    constructor
    · rintro ⟨function, rfl⟩
      refine ⟨(parameterFormEquivCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive).symm function, ?_⟩
      dsimp only
      rw [coerciveForm_norm_square_completion20261011]
      rfl
    · rintro ⟨function, rfl⟩
      refine ⟨parameterFormEquivCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive function, ?_⟩
      dsimp only
      rw [coerciveForm_norm_square_completion20261011]
      rfl
  rw [rangeEquality]
  exact identity

theorem parameterFormEvaluation_coefficient_completion20261011 {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (denominatorsPositive : ∀ index, 0 < 1 + (parameter - 1) * eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive
      (basis index) = eigenvalues index • basis index)
    (evaluation : StrongDual ℝ Energy) (index : Index) :
    parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive evaluation
      (parameterFormHilbertBasisCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive
        injective basis eigenvalues positive denominatorsPositive eigenvectors index) ^ 2 =
    ((eigenvalues index)⁻¹ * evaluation (baseCoercive.continuousLinearEquivOfBilin.symm
      (embedding.adjoint (basis index)))) ^ 2 / (parameter + (eigenvalues index)⁻¹ - 1) := by
  have lambdaPositive := parameterResolventEigenvalues_positive_completion20261011 parameter eigenvalues positive denominatorsPositive index
  have denominatorPositive : 0 < 1 + (parameter - 1) * eigenvalues index := by
    exact denominatorsPositive index
  rw [parameterFormHilbertBasisCompletion20261011, resolventEnergyHilbertBasis_apply_completion20261011]
  change (evaluation ((Real.sqrt (parameterResolventEigenvaluesCompletion20261011 parameter eigenvalues index))⁻¹ •
    parameterEnergySolutionCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterCoercive (basis index))) ^ 2 = _
  rw [map_smul, smul_eq_mul,
    parameterEnergySolution_eigenvalue_completion20261011 _ _ _ _ _ _ _ (positive index) (denominatorsPositive index) (eigenvectors index),
    map_smul, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt lambdaPositive.le,
    ← parameterResolventEigenvalues_inverse_completion20261011 parameter eigenvalues positive denominatorsPositive index, div_inv_eq_mul]
  dsimp [parameterResolventEigenvaluesCompletion20261011]
  field_simp [(positive index).ne', denominatorPositive.ne']

include parameterCoercive in
theorem parameterFormEvaluation_spectral_identity_completion20261011 {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (denominatorsPositive : ∀ index, 0 < 1 + (parameter - 1) * eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion20261011 embedding anchorEvaluation baseCoercive
      (basis index) = eigenvalues index • basis index)
    (evaluation : StrongDual ℝ Energy) :
    HasSum (fun index =>
      ((eigenvalues index)⁻¹ * evaluation (baseCoercive.continuousLinearEquivOfBilin.symm
        (embedding.adjoint (basis index)))) ^ 2 / (parameter + (eigenvalues index)⁻¹ - 1))
      (sSup (Set.range (fun function : Energy => evaluation function ^ 2 /
        parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter function function))) := by
  rw [parameterFormEvaluation_variational_completion20261011]
  have identity := parameterFormEvaluation_parseval_completion20261011 embedding anchorEvaluation baseCoercive
    parameter parameterCoercive injective basis eigenvalues positive denominatorsPositive eigenvectors evaluation
  simpa only [parameterFormEvaluation_coefficient_completion20261011] using identity

end
end IGSIII34.Spectral.PositiveParameter
