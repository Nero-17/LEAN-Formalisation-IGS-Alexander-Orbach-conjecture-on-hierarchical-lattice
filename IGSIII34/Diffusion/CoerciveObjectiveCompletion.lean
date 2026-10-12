import IGSIII34.Spectral.ParameterFormSpectrumCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section
open InnerProductSpace

variable {Energy : Type*} [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy]

def coerciveObjectiveCompletion
    (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ) (forcing : StrongDual ℝ Energy) (potential : Energy) : ℝ :=
  bilinear potential potential - 2 * forcing potential

theorem coerciveObjective_gap_completion
    (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ) (forcing : StrongDual ℝ Energy)
    (symmetric : ∀ first second, bilinear first second = bilinear second first)
    (solution : Energy) (variational : ∀ test, bilinear solution test = forcing test)
    (test : Energy) :
    coerciveObjectiveCompletion bilinear forcing test =
      coerciveObjectiveCompletion bilinear forcing solution + bilinear (test - solution) (test - solution) := by
  have expansion : bilinear test test = bilinear solution solution +
      2 * bilinear solution (test - solution) + bilinear (test - solution) (test - solution) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    rw [symmetric test solution]
    ring
  have forcingSplit : forcing test = forcing solution + forcing (test - solution) := by
    rw [map_sub]
    ring
  unfold coerciveObjectiveCompletion
  rw [expansion, forcingSplit]
  simp only [variational]
  ring

/-- A genuine variational solution is the unique minimizer of its actual
coercive quadratic objective; comparison at that one solution suffices. -/
theorem coerciveObjective_minimizer_unique_completion
    (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ) (coercive : IsCoercive bilinear)
    (forcing : StrongDual ℝ Energy)
    (symmetric : ∀ first second, bilinear first second = bilinear second first)
    (solution : Energy) (variational : ∀ test, bilinear solution test = forcing test)
    (candidate : Energy)
    (comparison : coerciveObjectiveCompletion bilinear forcing candidate ≤
      coerciveObjectiveCompletion bilinear forcing solution) : candidate = solution := by
  have gap := coerciveObjective_gap_completion bilinear forcing symmetric solution variational candidate
  have energyNonpositive : bilinear (candidate - solution) (candidate - solution) ≤ 0 := by linarith
  obtain ⟨constant, constantPositive, lower⟩ := coercive
  have normNonnegative := norm_nonneg (candidate - solution)
  have normZero : ‖candidate - solution‖ = 0 := by
    apply le_antisymm _ normNonnegative
    by_contra notZero
    have normPositive : 0 < ‖candidate - solution‖ := lt_of_not_ge notZero
    have productPositive := mul_pos (mul_pos constantPositive normPositive) normPositive
    linarith [lower (candidate - solution)]
  exact sub_eq_zero.mp (norm_eq_zero.mp normZero)

end
end IGSIII34.Diffusion


