import IGSIII34.Spectral.ParameterFormHilbertCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace IGSIII34.Diffusion

variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

theorem parameterFormEvaluation_quotient_bound_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (evaluation : StrongDual ℝ Energy)
    (function : Energy) :
    evaluation function ^ 2 /
      parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter function function ≤
      ‖parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne evaluation‖ ^ 2 := by
  have bound := evaluation_quotient_le_norm_square
    (parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne evaluation)
    ((parameterFormEquivCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne).symm function)
  rw [coerciveForm_norm_square_completion20261011] at bound
  exact bound

theorem parameterFormEvaluation_quotient_bddAbove_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (evaluation : StrongDual ℝ Energy) :
    BddAbove (Set.range (fun function : Energy => evaluation function ^ 2 /
      parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter function function)) := by
  refine ⟨‖parameterFormEvaluationCompletion20261011 embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne evaluation‖ ^ 2, ?_⟩
  rintro result ⟨function, rfl⟩
  exact parameterFormEvaluation_quotient_bound_completion20261011 _ _ _ _ _ _ _

end
end IGSIII34.Spectral
