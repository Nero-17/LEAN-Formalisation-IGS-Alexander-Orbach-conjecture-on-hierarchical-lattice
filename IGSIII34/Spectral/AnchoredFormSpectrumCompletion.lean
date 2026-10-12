import IGSIII34.Spectral.FormEigenbasisCompletion
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
  (coercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))

def anchoredFormEmbeddingCompletion :
    coerciveFormHilbertCompletion
      (anchoredResolventBilinearCompletion embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive →L[ℝ] L2 :=
  embedding.comp (coerciveFormEquivCompletion
    (anchoredResolventBilinearCompletion embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive).toContinuousLinearMap

def anchoredFormSolutionCompletion :
    L2 →L[ℝ] coerciveFormHilbertCompletion
      (anchoredResolventBilinearCompletion embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive :=
  (coerciveFormEquivCompletion
    (anchoredResolventBilinearCompletion embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive).symm.toContinuousLinearMap.comp
      (coercive.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embedding.adjoint)

theorem anchoredFormSolution_variational_completion
    (forcing : L2) (test : coerciveFormHilbertCompletion
      (anchoredResolventBilinearCompletion embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive) :
    inner ℝ (anchoredFormSolutionCompletion embedding anchorEvaluation coercive forcing) test =
      inner ℝ forcing (anchoredFormEmbeddingCompletion embedding anchorEvaluation coercive test) := by
  change anchoredResolventBilinearCompletion embedding anchorEvaluation
      (coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)) test =
    inner ℝ forcing (embedding test)
  exact anchoredL2Resolvent_variational_completion embedding anchorEvaluation coercive forcing test

theorem anchoredFormEmbedding_solution_completion (forcing : L2) :
    anchoredFormEmbeddingCompletion embedding anchorEvaluation coercive
      (anchoredFormSolutionCompletion embedding anchorEvaluation coercive forcing) =
        anchoredL2ResolventCompletion embedding anchorEvaluation coercive forcing := rfl

theorem anchoredFormEmbedding_injective_completion (injective : Function.Injective embedding) :
    Function.Injective (anchoredFormEmbeddingCompletion embedding anchorEvaluation coercive) :=
  injective.comp (coerciveFormEquivCompletion
    (anchoredResolventBilinearCompletion embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive).injective

def anchoredFormEvaluationCompletion (evaluation : StrongDual ℝ Energy) :
    StrongDual ℝ (coerciveFormHilbertCompletion
      (anchoredResolventBilinearCompletion embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive) :=
  evaluation.comp (coerciveFormEquivCompletion
    (anchoredResolventBilinearCompletion embedding anchorEvaluation)
    (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive).toContinuousLinearMap

def anchoredFormHilbertBasisCompletion {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion embedding anchorEvaluation coercive
      (basis index) = eigenvalues index • basis index) :
    HilbertBasis Index ℝ (coerciveFormHilbertCompletion
      (anchoredResolventBilinearCompletion embedding anchorEvaluation)
      (anchoredResolventBilinear_symmetric_completion embedding anchorEvaluation) coercive) :=
  resolventEnergyHilbertBasisCompletion
    (anchoredFormEmbeddingCompletion embedding anchorEvaluation coercive)
    (anchoredFormEmbedding_injective_completion embedding anchorEvaluation coercive injective)
    (anchoredFormSolutionCompletion embedding anchorEvaluation coercive)
    (anchoredFormSolution_variational_completion embedding anchorEvaluation coercive)
    basis eigenvalues positive (fun index => by
      rw [anchoredFormEmbedding_solution_completion]
      exact eigenvectors index)

theorem anchoredFormEvaluation_parseval_completion {Index : Type*}
    (injective : Function.Injective embedding) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion embedding anchorEvaluation coercive
      (basis index) = eigenvalues index • basis index)
    (evaluation : StrongDual ℝ Energy) :
    HasSum (fun index =>
      anchoredFormEvaluationCompletion embedding anchorEvaluation coercive evaluation
        (anchoredFormHilbertBasisCompletion embedding anchorEvaluation coercive
          injective basis eigenvalues positive eigenvectors index) ^ 2)
      (‖anchoredFormEvaluationCompletion embedding anchorEvaluation coercive evaluation‖ ^ 2) :=
  hilbert_basis_evaluation_parseval _ _

end
end IGSIII34.Spectral
