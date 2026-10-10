import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Universality
noncomputable section
open Filter
set_option maxHeartbeats 0

/-- A fixed sufficiently deep coarse scale admits an integer geodesic level
strictly inside any prescribed fractional distance window, with fixed margins. -/
theorem exists_power_window_level (length : ℕ) (hlength : 2 ≤ length)
    (lower upper : ℝ) (hlower : 0 < lower) (horder : lower < upper) (hupper : upper < 1)
    (margin : ℕ) :
    ∃ coarse index : ℕ, 2 ≤ index ∧ index < length ^ (coarse + 1) ∧
      (margin : ℝ) < lower * (length : ℝ) ^ (coarse + 1) ∧
      lower * (length : ℝ) ^ (coarse + 1) + margin < index ∧
      (index : ℝ) + margin < upper * (length : ℝ) ^ (coarse + 1) := by
  have hlengthReal : (1 : ℝ) < length := by exact_mod_cast (show 1 < length by omega)
  have hpower : Tendsto (fun coarse : ℕ => (length : ℝ) ^ (coarse + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hlengthReal).comp (tendsto_add_atTop_nat 1)
  have hwidth := (hpower.const_mul_atTop (sub_pos.mpr horder)).eventually
    (eventually_gt_atTop (2 * (margin : ℝ) + 2))
  have hleft := (hpower.const_mul_atTop hlower).eventually (eventually_gt_atTop (margin : ℝ))
  obtain ⟨coarse, hwidth, hleft⟩ := (hwidth.and hleft).exists
  let index := Nat.floor (lower * (length : ℝ) ^ (coarse + 1)) + margin + 2
  have hscale : 0 < (length : ℝ) ^ (coarse + 1) := pow_pos (zero_lt_one.trans hlengthReal) _
  have hfloorUpper := Nat.floor_le (mul_nonneg hlower.le hscale.le)
  have hfloorLower := Nat.lt_floor_add_one (lower * (length : ℝ) ^ (coarse + 1))
  have hindexCast : (index : ℝ) = Nat.floor (lower * (length : ℝ) ^ (coarse + 1)) + margin + 2 := by
    simp only [index, Nat.cast_add, Nat.cast_ofNat]
  have hfirst : lower * (length : ℝ) ^ (coarse + 1) + margin < index := by
    rw [hindexCast]
    linarith
  have hsecond : (index : ℝ) + margin < upper * (length : ℝ) ^ (coarse + 1) := by
    rw [hindexCast]
    nlinarith
  have hbeforeTerminal : (index : ℝ) < (length : ℝ) ^ (coarse + 1) := by
    have hmargin : (0 : ℝ) ≤ margin := Nat.cast_nonneg _
    have := mul_lt_mul_of_pos_right hupper hscale
    nlinarith
  refine ⟨coarse, index, by dsimp only [index]; omega, ?_, hleft, hfirst, hsecond⟩
  exact_mod_cast hbeforeTerminal

end
end Universality
