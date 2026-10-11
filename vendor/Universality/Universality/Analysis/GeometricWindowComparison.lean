import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section

/-- Removing a fixed number of terminal terms changes a positive geometric
sum by at most a constant, uniformly once one term remains. -/
theorem geometric_sum_extend_le (ratio : ℝ) (hratio : 0 ≤ ratio) (length delay : ℕ)
    (hlength : 1 ≤ length) :
    (∑ n ∈ Finset.range (length + delay), ratio ^ n) ≤
      (∑ j ∈ Finset.range (delay + 1), ratio ^ j) * ∑ n ∈ Finset.range length, ratio ^ n := by
  have hlast : ratio ^ (length - 1) ≤ ∑ n ∈ Finset.range length, ratio ^ n :=
    Finset.single_le_sum (fun n _ => pow_nonneg hratio n) (Finset.mem_range.mpr (by omega))
  induction delay with
  | zero => simp
  | succ delay ih =>
    have hterm : ratio ^ (length + delay) ≤ ratio ^ (delay + 1) *
        ∑ n ∈ Finset.range length, ratio ^ n := by
      calc
        _ = ratio ^ (delay + 1) * ratio ^ (length - 1) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := mul_le_mul_of_nonneg_left hlast (pow_nonneg hratio _)
    rw [show length + (delay + 1) = (length + delay) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ]
    nlinarith only [ih, hterm]

/-- A fixed initial segment and fixed terminal segment may both be removed
from a positive geometric sum without changing its order of magnitude. -/
theorem geometric_window_lower (ratio : ℝ) (hratio : 0 < ratio) (start delay : ℕ) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ length : ℕ, 1 ≤ length →
      lower * (∑ n ∈ Finset.range (length + start + delay), ratio ^ n) ≤
        ∑ n ∈ Finset.range length, ratio ^ (start + n) := by
  have hdenominator : 0 < ∑ n ∈ Finset.range (start + delay + 1), ratio ^ n := by
    have hh := Finset.single_le_sum (fun n _ => (pow_pos hratio n).le)
      (Finset.mem_range.mpr (by omega : 0 < start + delay + 1))
    simp only [pow_zero] at hh
    linarith
  refine ⟨ratio ^ start / (∑ n ∈ Finset.range (start + delay + 1), ratio ^ n),
    div_pos (pow_pos hratio _) hdenominator, ?_⟩
  intro length hlength
  have hb := geometric_sum_extend_le ratio hratio.le length (start + delay) hlength
  have hh := mul_le_mul_of_nonneg_left hb
    (div_nonneg (pow_nonneg hratio.le start) hdenominator.le)
  calc
    _ = (ratio ^ start / (∑ n ∈ Finset.range (start + delay + 1), ratio ^ n)) *
        (∑ n ∈ Finset.range (length + (start + delay)), ratio ^ n) := by rw [show length + start + delay = length + (start + delay) by omega]
    _ ≤ _ := hh
    _ = ∑ n ∈ Finset.range length, ratio ^ (start + n) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hdenominator.ne', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      exact (pow_add ratio start n).symm

end
end Universality
