import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace Universality
noncomputable section
open Finset
set_option maxHeartbeats 1000000

def logarithmLowerBound (x : ℝ) (n : ℕ) : ℝ :=
  2 * ∑ i ∈ range n, ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)

def logarithmUpperBound (x : ℝ) (n : ℕ) : ℝ :=
  logarithmLowerBound x n +
    2 * ((x - 1) / (x + 1)) ^ (2 * n + 1) / (1 - ((x - 1) / (x + 1)) ^ 2)

theorem logarithm_rational_bounds (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    logarithmLowerBound x n ≤ Real.log x ∧ Real.log x ≤ logarithmUpperBound x n := by
  have hpos : 0 < x + 1 := by linarith
  have hnonnegative : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) hpos.le
  have hlt : (x - 1) / (x + 1) < 1 := (div_lt_one hpos).mpr (by linarith)
  have hid : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    field_simp
    <;> ring
  have hl := Real.sum_range_le_log_div hnonnegative hlt n
  have hu := Real.log_div_le_sum_range_add hnonnegative hlt n
  rw [hid] at hl hu
  constructor
  · unfold logarithmLowerBound
    linarith
  · unfold logarithmUpperBound logarithmLowerBound
    rw [mul_div_assoc]
    linarith

end
end Universality
