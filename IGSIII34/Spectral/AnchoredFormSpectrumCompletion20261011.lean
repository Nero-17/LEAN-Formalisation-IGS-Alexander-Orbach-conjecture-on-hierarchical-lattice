import IGSIII34.Spectral.FormEigenbasisCompletion20261011
import IGSIII34.Spectral.HilbertEvaluation

/-! Constructing the energy-space eigenbasis and point-evaluation Parseval
identity from the Lax-Milgram resolvent of the anchored energy form. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace
open scoped Topology

variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]
  (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
  (coercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))

def anchoredFormEmbeddingCompletion20261011 :
    coerciveFormHilbertCompletion20261011
      (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive →L[ℝ] L2 :=
  embedding.comp (coerciveFormEquivCompletion20261011
    (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive).toContinuousLinearMap

def anchoredFormSolutionCompletion20261011 :
    L2 →L[ℝ] coerciveFormHilbertCompletion20261011
      (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive :=
  (coerciveFormEquivCompletion20261011
    (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive).symm.toContinuousLinearMap.comp
      (coercive.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embedding.adjoint)

theorem anchoredFormSolution_variational_completion20261011
    (forcing : L2) (test : coerciveFormHilbertCompletion20261011
      (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive) :
    inner ℝ (anchoredFormSolutionCompletion20261011 embedding anchorEvaluation coercive forcing) test =
      inner ℝ forcing (anchoredFormEmbeddingCompletion20261011 embedding anchorEvaluation coercive test) := by
  change anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation
      (coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)) test =
    inner ℝ forcing (embedding test)
  exact anchoredL2Resolvent_variational_completion20261011 embedding anchorEvaluation coercive forcing test

theorem anchoredFormEmbedding_solution_completion20261011 (forcing : L2) :
    anchoredFormEmbeddingCompletion20261011 embedding anchorEvaluation coercive
      (anchoredFormSolutionCompletion20261011 embedding anchorEvaluation coercive forcing) =
        anchoredL2ResolventCompletion20261011 embedding anchorEvaluation coercive forcing := rfl

theorem anchoredFormEmbedding_injective_completion20261011 (injective : Function.Injective embedding) :
    Function.Injective (anchoredFormEmbeddingCompletion20261011 embedding anchorEvaluation coercive) :=
  injective.comp (coerciveFormEquivCompletion20261011
    (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive).injective

def anchoredFormEvaluationCompletion20261011 (evaluation : StrongDual ℝ Energy) :
    StrongDual ℝ (coerciveFormHilbertCompletion20261011
      (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive) :=
  evaluation.comp (coerciveFormEquivCompletion20261011
    (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive).toContinuousLinearMap

def anchoredFormHilbertBasisCompletion20261011 {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion20261011 embedding anchorEvaluation coercive
      (basis index) = eigenvalues index • basis index) :
    HilbertBasis Index ℝ (coerciveFormHilbertCompletion20261011
      (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation) coercive) :=
  resolventEnergyHilbertBasisCompletion20261011
    (anchoredFormEmbeddingCompletion20261011 embedding anchorEvaluation coercive)
    (anchoredFormEmbedding_injective_completion20261011 embedding anchorEvaluation coercive injective)
    (anchoredFormSolutionCompletion20261011 embedding anchorEvaluation coercive)
    (anchoredFormSolution_variational_completion20261011 embedding anchorEvaluation coercive)
    basis eigenvalues positive (fun index => by
      rw [anchoredFormEmbedding_solution_completion20261011]
      exact eigenvectors index)

theorem anchoredFormEvaluation_parseval_completion20261011 {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion20261011 embedding anchorEvaluation coercive
      (basis index) = eigenvalues index • basis index)
    (evaluation : StrongDual ℝ Energy) :
    HasSum (fun index =>
      anchoredFormEvaluationCompletion20261011 embedding anchorEvaluation coercive evaluation
        (anchoredFormHilbertBasisCompletion20261011 embedding anchorEvaluation coercive
          injective basis eigenvalues positive eigenvectors index) ^ 2)
      (‖anchoredFormEvaluationCompletion20261011 embedding anchorEvaluation coercive evaluation‖ ^ 2) :=
  hilbert_basis_evaluation_parseval _ _

end
end IGSIII34.Spectral
