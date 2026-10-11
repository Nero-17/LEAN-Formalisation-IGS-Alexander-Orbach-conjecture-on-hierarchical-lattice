import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Integer moment checks for compressed leaf allocations

The data checks in this directory are arithmetic certificates.  They do not
by themselves prove that a graph has the certified critical mass.  That needs
the word-allocation and matrix-recursion bridges.
-/

namespace Universality.Certificates

/-- Horner evaluation of the zero-count totals, in increasing degree order. -/
def integerMoment (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | coefficient :: rest => coefficient + base * integerMoment base rest

theorem integerMoment_eq_sum (base : ℕ) (coefficients : List ℕ) :
    integerMoment base coefficients =
      ∑ i : Fin coefficients.length, coefficients[i.val] * base ^ i.val := by
  induction coefficients with
  | nil => simp [integerMoment]
  | cons coefficient rest ih =>
      rw [integerMoment, ih]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.getElem_cons_zero, Fin.val_zero, pow_zero, mul_one,
        Fin.val_succ, List.getElem_cons_succ]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring

structure IntegerMomentCertificate where
  depth : ℕ
  base : ℕ
  scaleOffset : ℕ := 0
  zeroTotals : List ℕ

def IntegerMomentCertificate.valid (C : IntegerMomentCertificate) : Prop :=
  C.zeroTotals.length = C.depth + 1 ∧
    2 ^ C.depth + C.zeroTotals.getLast! = C.base ^ 100 + C.scaleOffset ∧
    5 ^ C.depth + 4 * integerMoment 2 C.zeroTotals = C.base ^ 232 ∧
    8 * 13 ^ C.depth + 5 * integerMoment 6 C.zeroTotals =
      8 ^ (C.depth + 1) * C.base ^ 70

instance (C : IntegerMomentCertificate) : Decidable C.valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Universality.Certificates
