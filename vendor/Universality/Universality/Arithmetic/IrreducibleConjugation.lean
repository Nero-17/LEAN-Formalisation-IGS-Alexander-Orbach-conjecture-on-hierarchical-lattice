import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.LinearCombination

/-!
The nonsplit quadratic mass argument, separated from graph extraction.
No automorphism of the real field is postulated: polynomial divisibility sends
a power relation at the Perron root to its other quadratic root.
-/

namespace Universality.Section4

open Polynomial

theorem nonsplit_quadratic_minpoly
    (base : Subfield ℝ) (trace determinant : base) (root : ℝ)
    (hroot : root ^ 2 - (trace : ℝ) * root + (determinant : ℝ) = 0)
    (hnonsplit : root ∉ base) :
    minpoly base root = X ^ 2 - C trace * X + C determinant := by
  have hmonic : (X ^ 2 - C trace * X + C determinant : base[X]).Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one (n := 2)
    · compute_degree
    · simp
  have hannihilates :
      (aeval root) (X ^ 2 - C trace * X + C determinant : base[X]) = 0 := by
    simpa [Subfield.algebraMap_ofSubfield] using hroot
  have hintegral : IsIntegral base root := ⟨_, hmonic, hannihilates⟩
  have hdegree : 2 ≤ (minpoly base root).natDegree := by
    apply (minpoly.two_le_natDegree_iff hintegral).mpr
    rintro ⟨value, hvalue⟩
    exact hnonsplit (hvalue ▸ value.property)
  apply (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintegral) hmonic
    (minpoly.dvd base root hannihilates) ?_).symm
  exact (by compute_degree : (X ^ 2 - C trace * X + C determinant : base[X]).natDegree ≤ 2)
    |>.trans hdegree

theorem nonsplit_quadratic_positive_power_not_mem
    (base : Subfield ℝ) (trace determinant : base) (root conjugate : ℝ)
    (hroot : root ^ 2 - (trace : ℝ) * root + (determinant : ℝ) = 0)
    (hconjugate : conjugate ^ 2 - (trace : ℝ) * conjugate + (determinant : ℝ) = 0)
    (hnonsplit : root ∉ base) (hrootPositive : 0 < root)
    (hsmaller : |conjugate| < root) (exponent : ℕ) (hexponent : 0 < exponent) :
    root ^ exponent ∉ base := by
  intro hpower
  have hannihilates :
      (aeval root) (X ^ exponent - C (⟨root ^ exponent, hpower⟩ : base)) = 0 := by
    simp [Subfield.algebraMap_ofSubfield]
  have hdivides := minpoly.dvd base root hannihilates
  rw [nonsplit_quadratic_minpoly base trace determinant root hroot hnonsplit] at hdivides
  have hconjugateRoot :
      (aeval conjugate) (X ^ 2 - C trace * X + C determinant : base[X]) = 0 := by
    simpa [Subfield.algebraMap_ofSubfield] using hconjugate
  have hconjugatePower :=
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap base ℝ) conjugate hdivides hconjugateRoot
  have hequal : conjugate ^ exponent = root ^ exponent := by
    simpa [Subfield.algebraMap_ofSubfield, sub_eq_zero] using hconjugatePower
  have habsequal := congrArg abs hequal
  rw [abs_pow, abs_pow, abs_of_pos hrootPositive] at habsequal
  exact (ne_of_lt (pow_lt_pow_left₀ hsmaller (abs_nonneg conjugate) (by omega))) habsequal

theorem nonsplit_quadratic_integer_power_not_mem
    (base : Subfield ℝ) (trace determinant : base) (root conjugate : ℝ)
    (hroot : root ^ 2 - (trace : ℝ) * root + (determinant : ℝ) = 0)
    (hconjugate : conjugate ^ 2 - (trace : ℝ) * conjugate + (determinant : ℝ) = 0)
    (hnonsplit : root ∉ base) (hrootPositive : 0 < root)
    (hsmaller : |conjugate| < root) (exponent : ℤ) (hexponent : exponent ≠ 0) :
    root ^ exponent ∉ base := by
  cases exponent with
  | ofNat exponent =>
      simpa using nonsplit_quadratic_positive_power_not_mem base trace determinant root conjugate
        hroot hconjugate hnonsplit hrootPositive hsmaller exponent
          (Nat.pos_of_ne_zero (fun hzero => hexponent (by simp [hzero])))
  | negSucc exponent =>
      intro hpower
      have hinverse := base.inv_mem hpower
      simp only [zpow_negSucc, inv_inv] at hinverse
      exact nonsplit_quadratic_positive_power_not_mem base trace determinant root conjugate
        hroot hconjugate hnonsplit hrootPositive hsmaller (exponent + 1) (by omega) hinverse

end Universality.Section4
