import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

/-!
# Ordered binary words and noncommutative expansions

The order of matrix factors is retained throughout.  These identities justify
the compressed word sums used by the Section 5 integer certificates.
-/

namespace Universality

def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (binaryWords n).map (false :: ·) ++ (binaryWords n).map (true :: ·)

theorem binaryWords_length (n : ℕ) : (binaryWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binaryWords, ih, pow_succ, Nat.mul_two]

theorem word_length_of_mem_binaryWords {n : ℕ} {w : List Bool}
    (hw : w ∈ binaryWords n) : w.length = n := by
  induction n generalizing w with
  | zero => simpa [binaryWords] using hw
  | succ n ih =>
      simp only [binaryWords, List.mem_append, List.mem_map] at hw
      rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

def wordProduct {R : Type*} [Monoid R] (K J : R) : List Bool → R
  | [] => 1
  | false :: w => K * wordProduct K J w
  | true :: w => J * wordProduct K J w

theorem wordProduct_append {R : Type*} [Monoid R] (K J : R) (u v : List Bool) :
    wordProduct K J (u ++ v) = wordProduct K J u * wordProduct K J v := by
  induction u with
  | nil => simp [wordProduct]
  | cons b u ih => cases b <;> simp [wordProduct, ih, mul_assoc]

theorem sum_wordProducts {R : Type*} [Semiring R] (K J : R) (n : ℕ) :
    ((binaryWords n).map (wordProduct K J)).sum = (K + J) ^ n := by
  induction n with
  | zero => simp [binaryWords, wordProduct]
  | succ n ih =>
      simp only [binaryWords, List.map_append, List.map_map, List.sum_append,
        Function.comp_def, wordProduct, List.sum_map_mul_left, ih]
      rw [← add_mul, pow_succ']

end Universality
