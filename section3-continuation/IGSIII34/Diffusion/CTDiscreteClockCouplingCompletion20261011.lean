import IGSIII34.Diffusion.ClockGridInterpolationCompletion20261011
import IGSIII34.Diffusion.FlooredIntervalModulusCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology

/-- The genuine holding-clock walk and the fixed-floor walk are uniformly
close on the same trajectory whenever the proved chain modulus and
inverse-clock bounds hold. This also controls the interval endpoint. -/
theorem finiteChain_good_clock_coupling_completion20261011
    {Vertex Space : Type*} [MetricSpace Space] (placement : Vertex → Space)
    (trajectory : ℕ → Vertex) (holdingTimes : ℕ → ℝ)
    (acceleration : ℝ) (accelerationPositive : 0 < acceleration)
    (horizon : ℕ) (duration error tolerance : ℝ)
    (errorSmall : error ≤ duration) (errorAtMostOne : error ≤ 1)
    (good : trajectory ∉ finiteIntervalChainBadModulusCompletion20261011 placement acceleration (horizon + 1 : ℕ) duration tolerance)
    (clockError : ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
      |(holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration - time| ≤ error)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    dist (placement (holdingTimePath trajectory holdingTimes (acceleration * time)))
      (placement (trajectory ⌊acceleration * time⌋₊)) ≤ tolerance := by
  let index := holdingJumpIndex holdingTimes (acceleration * time)
  have clock := clockError time timeNonnegative timeBound
  change |(index : ℝ) / acceleration - time| ≤ error at clock
  have capNonnegative : 0 ≤ acceleration * (horizon + 1 : ℕ) :=
    mul_nonneg accelerationPositive.le (Nat.cast_nonneg _)
  have upper : (index : ℝ) ≤ acceleration * (horizon + 1 : ℕ) := by
    rw [mul_comm]
    apply (div_le_iff₀ accelerationPositive).mp
    have upper := (abs_le.mp clock).2
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have indexCap : index ≤ ⌊acceleration * (horizon + 1 : ℕ)⌋₊ :=
    (Nat.le_floor_iff capNonnegative).mpr upper
  have floorCap : ⌊acceleration * time⌋₊ ≤ ⌊acceleration * (horizon + 1 : ℕ)⌋₊ := by
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_left _ accelerationPositive.le
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have normalized : ((index : ℝ) - acceleration * time) / acceleration =
      (index : ℝ) / acceleration - time := by
    field_simp
  have clockScaled : |(index : ℝ) - acceleration * time| ≤ error * acceleration := by
    rw [← normalized, abs_div, abs_of_pos accelerationPositive] at clock
    exact (div_le_iff₀ accelerationPositive).mp clock
  have floorError := Nat.abs_sub_floor_le (mul_nonneg accelerationPositive.le timeNonnegative)
  have difference : |(index : ℝ) - ⌊acceleration * time⌋₊| ≤ acceleration * duration + 1 := by
    calc
      _ ≤ |(index : ℝ) - acceleration * time| + |acceleration * time - ⌊acceleration * time⌋₊| := abs_sub_le _ _ _
      _ ≤ error * acceleration + 1 := add_le_add clockScaled floorError
      _ ≤ acceleration * duration + 1 := by
        simpa only [mul_comm] using add_le_add (mul_le_mul_of_nonneg_right errorSmall accelerationPositive.le) le_rfl
  by_contra failure
  exact good ⟨index, indexCap, ⌊acceleration * time⌋₊, floorCap, difference, lt_of_not_ge failure⟩

end
end IGSIII34.Diffusion
