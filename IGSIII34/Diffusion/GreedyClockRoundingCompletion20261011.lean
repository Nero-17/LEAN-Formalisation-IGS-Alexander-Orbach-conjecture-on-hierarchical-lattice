import IGSIII34.Diffusion.FlooredObservationModulusCompletion20261011
import IGSIII34.Diffusion.GreedyModulusParameterSelectionCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section

theorem greedy_clock_rounding_completion20261011
    (acceleration horizon largeDuration smallDuration : ℝ) (steps : ℕ)
    (accelerationPositive : 0 < acceleration) (horizonNonnegative : 0 ≤ horizon)
    (largeDurationPositive : 0 < largeDuration) (smallDurationPositive : 0 < smallDuration)
    (stepsPositive : 0 < steps) (largeGap : 4 * horizon + 1 < steps * largeDuration)
    (clockLarge : 2 * (steps : ℝ) ≤ acceleration) (clockSmall : 4 ≤ acceleration * smallDuration) :
    (⌊acceleration * largeDuration⌋₊ : ℝ) ≤ acceleration * largeDuration ∧
      (⌈acceleration * (smallDuration / 2) + 1⌉₊ : ℝ) ≤ acceleration * smallDuration ∧
      2 * (⌊acceleration * horizon⌋₊ : ℝ) <
        (steps : ℝ) * ⌊acceleration * largeDuration⌋₊ := by
  have floorUpper := Nat.floor_le (show 0 ≤ acceleration * largeDuration by positivity)
  have ceilUpper := Nat.ceil_lt_add_one (show 0 ≤ acceleration * (smallDuration / 2) + 1 by positivity)
  have floorLower := Nat.lt_floor_add_one (acceleration * largeDuration)
  have horizonUpper := Nat.floor_le (show 0 ≤ acceleration * horizon by positivity)
  have stepsRealPositive : (0 : ℝ) < steps := by exact_mod_cast stepsPositive
  have multipliedGap := mul_lt_mul_of_pos_left largeGap accelerationPositive
  have multipliedFloor := mul_lt_mul_of_pos_left floorLower stepsRealPositive
  refine ⟨floorUpper, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem greedy_clock_exit_factor_completion20261011
    (horizon window steps : ℕ) (halfGap : 2 * (horizon : ℝ) < steps * window)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) :
    (window : ℝ) * steps * bound / ((steps : ℝ) * window - horizon) ≤ 2 * bound := by
  have denominatorPositive : 0 < (steps : ℝ) * window - horizon := by
    have : (0 : ℝ) ≤ horizon := Nat.cast_nonneg _
    linarith
  apply (div_le_iff₀ denominatorPositive).mpr
  have multiplied := mul_le_mul_of_nonneg_right halfGap.le boundNonnegative
  nlinarith

end
end IGSIII34.Diffusion
