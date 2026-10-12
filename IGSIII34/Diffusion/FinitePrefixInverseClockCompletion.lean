import IGSIII34.Diffusion.HoldingTimePaths

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped _root_.Topology

/-- A bounded cumulative-clock event already controls the inverse clock at
all real times; there is no stopping-time premise. -/
theorem holdingJumpIndex_uniform_of_finite_prefix_completion
    (holding : ℕ → ℝ) (positive : ∀ index, 0 < holding index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holding) atTop atTop)
    (acceleration horizon tolerance : ℝ) (accelerationLarge : 2 < acceleration)
    (horizonNonnegative : 0 ≤ horizon) (toleranceNonnegative : 0 ≤ tolerance) (toleranceSmall : tolerance ≤ 1 / 2)
    (good : ∀ count ≤ ⌊acceleration * (horizon + 1)⌋₊,
      |cumulativeHoldingTime holding count - count| ≤ acceleration * tolerance)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    |(holdingJumpIndex holding (acceleration * time) : ℝ) / acceleration - time| ≤ tolerance + 1 / acceleration := by
  have accelerationPositive : 0 < acceleration := by linarith
  let cutoff := ⌊acceleration * (horizon + 1)⌋₊
  have floorLower : acceleration * (horizon + 1) - 1 < (cutoff : ℝ) := by
    have result := Nat.lt_floor_add_one (acceleration * (horizon + 1))
    dsimp only [cutoff]
    linarith
  have cutoffError := (abs_le.mp (good cutoff le_rfl)).1
  have cutoffAfter : acceleration * horizon < cumulativeHoldingTime holding cutoff := by
    nlinarith
  have interval := holdingJumpIndex_interval holding (fun index => (positive index).le)
    nonexplosion (acceleration * time) (mul_nonneg accelerationPositive.le timeNonnegative)
  have indexBelow : holdingJumpIndex holding (acceleration * time) < cutoff := by
    apply lt_of_not_ge
    intro large
    have clock := cumulativeHoldingTime_monotone holding (fun index => (positive index).le) large
    have timeScaled := mul_le_mul_of_nonneg_left timeBound accelerationPositive.le
    linarith
  have first := abs_le.mp (good (holdingJumpIndex holding (acceleration * time)) indexBelow.le)
  have next := abs_le.mp (good (holdingJumpIndex holding (acceleration * time) + 1) indexBelow)
  simp only [Nat.cast_add, Nat.cast_one] at next
  have upper : (holdingJumpIndex holding (acceleration * time) : ℝ) - acceleration * time ≤ acceleration * tolerance := by
    linarith [interval.1, first.1]
  have lower : acceleration * time - (holdingJumpIndex holding (acceleration * time) : ℝ) ≤ acceleration * tolerance + 1 := by
    linarith [interval.2, next.2]
  rw [abs_le]
  constructor
  · have divided := div_le_div_of_nonneg_right lower accelerationPositive.le
    have identity : (acceleration * time - (holdingJumpIndex holding (acceleration * time) : ℝ)) / acceleration =
        time - (holdingJumpIndex holding (acceleration * time) : ℝ) / acceleration := by field_simp <;> ring
    have target : (acceleration * tolerance + 1) / acceleration = tolerance + 1 / acceleration := by field_simp <;> ring
    rw [identity, target] at divided
    linarith
  · have divided := div_le_div_of_nonneg_right upper accelerationPositive.le
    have identity : ((holdingJumpIndex holding (acceleration * time) : ℝ) - acceleration * time) / acceleration =
        (holdingJumpIndex holding (acceleration * time) : ℝ) / acceleration - time := by field_simp <;> ring
    have target : (acceleration * tolerance) / acceleration = tolerance := by field_simp
    rw [identity, target] at divided
    exact divided.trans (le_add_of_nonneg_right (one_div_nonneg.mpr accelerationPositive.le))

end
end IGSIII34.Diffusion
