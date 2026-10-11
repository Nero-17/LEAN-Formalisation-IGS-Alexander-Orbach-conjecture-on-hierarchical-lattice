import IGSIII34.Diffusion.TwoCoverGreedyModulusCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace IGSIII34.Diffusion
noncomputable section
open Filter

/-- The large-window exit count and the tiny-gap union can both be made
small using independent resolvent parameters. The second approximation
error is selected only after the number of greedy exits has been fixed. -/
theorem exists_two_cover_modulus_parameters_completion20261011
    (labels horizon probability : ℝ) (labelsPositive : 0 < labels)
    (horizonNonnegative : 0 ≤ horizon) (probabilityPositive : 0 < probability)
    (parameter : ℝ → ℝ) (parameterPositive : ∀ error, 0 < error → 0 < parameter error) :
    ∃ largeError largeDuration : ℝ, ∃ steps : ℕ, ∃ smallError smallDuration : ℝ,
      0 < largeError ∧ 0 < largeDuration ∧ 0 < steps ∧ 0 < smallError ∧ 0 < smallDuration ∧
      4 * horizon + 1 < steps * largeDuration ∧
      2 * (2 * labels * (largeError + 2 * parameter largeError * largeDuration)) +
        steps * (2 * labels * (smallError + 2 * parameter smallError * smallDuration)) < probability := by
  let largeError := probability / (32 * labels)
  have largeErrorPositive : 0 < largeError := by dsimp only [largeError]; positivity
  have largeParameterPositive := parameterPositive largeError largeErrorPositive
  let largeDuration := probability / (64 * labels * parameter largeError)
  have largeDurationPositive : 0 < largeDuration := by dsimp only [largeDuration]; positivity
  obtain ⟨steps, largeSteps⟩ := exists_nat_gt ((4 * horizon + 1) / largeDuration)
  have stepsPositive : 0 < steps := by
    have quotientPositive : 0 < (4 * horizon + 1) / largeDuration := by positivity
    have realPositive : (0 : ℝ) < steps := quotientPositive.trans largeSteps
    exact_mod_cast realPositive
  have realStepsPositive : (0 : ℝ) < steps := by exact_mod_cast stepsPositive
  let smallError := probability / (16 * labels * steps)
  have smallErrorPositive : 0 < smallError := by dsimp only [smallError]; positivity
  have smallParameterPositive := parameterPositive smallError smallErrorPositive
  let smallDuration := probability / (32 * labels * steps * parameter smallError)
  have smallDurationPositive : 0 < smallDuration := by dsimp only [smallDuration]; positivity
  refine ⟨largeError, largeDuration, steps, smallError, smallDuration,
    largeErrorPositive, largeDurationPositive, stepsPositive, smallErrorPositive, smallDurationPositive,
    (by exact (div_lt_iff₀ largeDurationPositive).mp largeSteps), ?_⟩
  have identity : 2 * (2 * labels * (largeError + 2 * parameter largeError * largeDuration)) +
      steps * (2 * labels * (smallError + 2 * parameter smallError * smallDuration)) = probability / 2 := by
    have largeProduct : parameter largeError * largeDuration = probability / (64 * labels) := by
      dsimp only [largeDuration]
      field_simp [labelsPositive.ne', largeParameterPositive.ne']
      <;> ring
    have smallProduct : parameter smallError * smallDuration = probability / (32 * labels * steps) := by
      dsimp only [smallDuration]
      field_simp [labelsPositive.ne', realStepsPositive.ne', smallParameterPositive.ne']
      <;> ring
    rw [mul_assoc 2 (parameter largeError), largeProduct,
      mul_assoc 2 (parameter smallError), smallProduct]
    dsimp only [largeError, smallError]
    field_simp [labelsPositive.ne', realStepsPositive.ne']
    <;> ring
  rw [identity]
  linarith

end
end IGSIII34.Diffusion
