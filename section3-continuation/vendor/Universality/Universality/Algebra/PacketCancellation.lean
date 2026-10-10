import Universality.Algebra.WordExpansion
import Universality.Matrix.TwoByTwo
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Signed paired words

Each binary choice stands for 01 or 10, with opposite signs.  Summing the
ordered products gives a power of the commutator.  For the Wheatstone kernels
the square of that commutator is 18 times the identity.
-/

namespace Universality

def pairedWord : List Bool → List Bool
  | [] => []
  | false :: w => false :: true :: pairedWord w
  | true :: w => true :: false :: pairedWord w

def wordSign : List Bool → ℤ
  | [] => 1
  | false :: w => wordSign w
  | true :: w => -wordSign w

theorem pairedWord_length (w : List Bool) : (pairedWord w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [pairedWord, ih] <;> omega

theorem wordProduct_signedPair {R : Type*} [Ring R] (K J : R) (w : List Bool) :
    wordProduct (K * J) (-(J * K)) w =
      wordSign w • wordProduct K J (pairedWord w) := by
  induction w with
  | nil => simp [wordProduct, wordSign, pairedWord]
  | cons b w ih =>
      cases b <;> simp only [wordProduct, wordSign, pairedWord, ih,
        mul_smul_comm, neg_smul, neg_mul, mul_assoc, smul_neg]

theorem signed_packet_sum {R : Type*} [Ring R] (K J : R) (n : ℕ) :
    ((binaryWords n).map fun w => wordSign w • wordProduct K J (pairedWord w)).sum =
      (K * J - J * K) ^ n := by
  simp_rw [← wordProduct_signedPair]
  simpa only [sub_eq_add_neg] using sum_wordProducts (K * J) (-(J * K)) n

def outerKernelNumerator : Matrix (Fin 2) (Fin 2) ℤ := !![22, 18; 5, 18]
def centralKernelNumerator : Matrix (Fin 2) (Fin 2) ℤ := !![9, 12; 3, 6]

theorem wheatstone_commutator :
    outerKernelNumerator * centralKernelNumerator -
      centralKernelNumerator * outerKernelNumerator = !![-6, -6; 3, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [outerKernelNumerator,
    centralKernelNumerator, Matrix.mul_apply, Fin.sum_univ_two]

theorem wheatstone_commutator_square :
    (outerKernelNumerator * centralKernelNumerator -
      centralKernelNumerator * outerKernelNumerator) ^ 2 = (18 : ℤ) • 1 := by
  rw [wheatstone_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem wheatstone_commutator_odd_power (n : ℕ) :
    (outerKernelNumerator * centralKernelNumerator -
      centralKernelNumerator * outerKernelNumerator) ^ (2 * n + 1) =
      (18 ^ n : ℤ) •
        (outerKernelNumerator * centralKernelNumerator -
          centralKernelNumerator * outerKernelNumerator) := by
  rw [pow_succ, pow_mul, wheatstone_commutator_square, smul_pow, one_pow,
    smul_mul_assoc, one_mul]

theorem signed_wheatstone_packet (n : ℕ) :
    ((binaryWords (2 * n + 1)).map fun w => wordSign w •
      wordProduct outerKernelNumerator centralKernelNumerator (pairedWord w)).sum =
      (18 ^ n : ℤ) • !![-6, -6; 3, 6] := by
  rw [signed_packet_sum, wheatstone_commutator_odd_power, wheatstone_commutator]

end Universality
