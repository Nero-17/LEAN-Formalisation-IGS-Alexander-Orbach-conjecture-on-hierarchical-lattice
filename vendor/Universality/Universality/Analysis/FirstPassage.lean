import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic

namespace Universality
noncomputable section

def firstPassageBelow (sequence : ℕ → ℝ) (threshold : ℝ) : ℕ := by
  classical
  exact if hexists : ∃ n, sequence n ≤ threshold then Nat.find hexists else 0

theorem firstPassageBelow_spec (sequence : ℕ → ℝ) (threshold : ℝ)
    (hexists : ∃ n, sequence n ≤ threshold) :
    sequence (firstPassageBelow sequence threshold) ≤ threshold := by
  rw [firstPassageBelow, dif_pos hexists]
  exact Nat.find_spec hexists

theorem firstPassageBelow_minimal (sequence : ℕ → ℝ) (threshold : ℝ)
    (hexists : ∃ n, sequence n ≤ threshold) (n : ℕ) (hn : n < firstPassageBelow sequence threshold) :
    threshold < sequence n := by
  rw [firstPassageBelow, dif_pos hexists] at hn
  exact lt_of_not_ge (Nat.find_min hexists hn)

theorem firstPassageBelow_pos (sequence : ℕ → ℝ) (threshold : ℝ)
    (hexists : ∃ n, sequence n ≤ threshold) (hstart : threshold < sequence 0) :
    0 < firstPassageBelow sequence threshold := by
  by_contra h
  have heq : firstPassageBelow sequence threshold = 0 := Nat.eq_zero_of_not_pos h
  have hspec := firstPassageBelow_spec sequence threshold hexists
  rw [heq] at hspec
  exact (not_le_of_gt hstart) hspec

end
end Universality
