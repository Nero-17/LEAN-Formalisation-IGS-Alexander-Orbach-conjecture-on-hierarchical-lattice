import Universality.Algebra.WordExpansion
import Mathlib.Algebra.Module.Basic

namespace Universality

def zeroCount (w : List Bool) : ℕ := w.count false

@[simp] theorem zeroCount_false_cons (w : List Bool) :
    zeroCount (false :: w) = zeroCount w + 1 := by simp [zeroCount]

@[simp] theorem zeroCount_true_cons (w : List Bool) :
    zeroCount (true :: w) = zeroCount w := by simp [zeroCount]

def groupedWordSum {R : Type*} [Semiring R] (K J : R) (n z : ℕ) : R :=
  ((binaryWords n).map fun w => if zeroCount w = z then wordProduct K J w else 0).sum

theorem conditional_left_mul {R : Type*} [Semiring R] (p : Prop) [Decidable p]
    (a b : R) : (if p then a * b else 0) = a * (if p then b else 0) := by
  split_ifs <;> simp

theorem groupedWordSum_zero {R : Type*} [Semiring R] (K J : R) (z : ℕ) :
    groupedWordSum K J 0 z = if z = 0 then 1 else 0 := by
  simp [groupedWordSum, binaryWords, zeroCount, wordProduct, eq_comm]

theorem groupedWordSum_succ_zero {R : Type*} [Semiring R] (K J : R) (n : ℕ) :
    groupedWordSum K J (n + 1) 0 = J * groupedWordSum K J n 0 := by
  simp only [groupedWordSum, binaryWords, List.map_append, List.map_map,
    List.sum_append, Function.comp_def, zeroCount_false_cons,
    zeroCount_true_cons, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false, List.map_const', List.sum_replicate,
    smul_zero, zero_add, wordProduct]
  simp_rw [conditional_left_mul]
  exact List.sum_map_mul_left _ _ _

theorem groupedWordSum_succ_succ {R : Type*} [Semiring R] (K J : R) (n z : ℕ) :
    groupedWordSum K J (n + 1) (z + 1) =
      K * groupedWordSum K J n z + J * groupedWordSum K J n (z + 1) := by
  simp only [groupedWordSum, binaryWords, List.map_append, List.map_map,
    List.sum_append, Function.comp_def, zeroCount_false_cons,
    zeroCount_true_cons, Nat.add_right_cancel_iff,
    wordProduct]
  congr 1
  · simp_rw [conditional_left_mul]
    exact List.sum_map_mul_left _ _ _
  · simp_rw [conditional_left_mul]
    exact List.sum_map_mul_left _ _ _

theorem wordProduct_scaled_left {R : Type*} [Semiring R]
    (K J : R) (weight : ℕ) (w : List Bool) :
    wordProduct (weight • K) J w = weight ^ zeroCount w • wordProduct K J w := by
  induction w with
  | nil => simp [wordProduct, zeroCount]
  | cons b w ih =>
      cases b
      · simp only [wordProduct, ih, zeroCount, List.count_cons_self, pow_succ,
          smul_mul_smul]
        rw [Nat.mul_comm]
      · simp only [wordProduct, ih, zeroCount,
          List.count_cons_of_ne (by decide : true ≠ false), mul_smul_comm]

theorem weighted_word_sum {R : Type*} [Semiring R] (K J : R) (weight n : ℕ) :
    ((binaryWords n).map fun w => weight ^ zeroCount w • wordProduct K J w).sum =
      (weight • K + J) ^ n := by
  simp_rw [← wordProduct_scaled_left]
  exact sum_wordProducts _ _ n

end Universality
