import Universality.Arithmetic.FixedPointPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat

namespace Universality.Section4

open Polynomial

/-- The coefficient at the resonant index rules out this polynomial differential
equation. This is the arithmetic obstruction behind integer fixed-point multipliers. -/
theorem polynomial_integer_multiplier_obstruction (fixedPoint : ℚ[X])
    (index : ℕ) (hindex : 0 < index) (hzero : fixedPoint.eval 0 = -1)
    (hequation : X * (1 - X) * fixedPoint.derivative =
      C (index : ℚ) + C (index : ℚ) * (1 - 2 * X) * fixedPoint) : False := by
  have hcoefficients (n : ℕ) :
      ((n + 1 : ℕ) - (index : ℚ)) * fixedPoint.coeff (n + 1) =
        ((n : ℚ) - 2 * index) * fixedPoint.coeff n := by
    have hcoeff := congrArg (fun polynomial : ℚ[X] => polynomial.coeff (n + 1)) hequation
    have hshift : (X * fixedPoint.derivative).coeff n = (n : ℚ) * fixedPoint.coeff n := by
      cases n with
      | zero => simp
      | succ n => simp [coeff_X_mul, coeff_derivative, mul_comm]
    simp [mul_sub, sub_mul, mul_assoc, coeff_X_mul,
      coeff_derivative, hshift] at hcoeff
    push_cast
    linear_combination hcoeff
  have hnonzero : ∀ n : ℕ, n < index → fixedPoint.coeff n ≠ 0 := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa only [coeff_zero_eq_eval_zero, hzero, ne_eq, neg_eq_zero] using
          (one_ne_zero : (1 : ℚ) ≠ 0)
    | succ n hinduction =>
        intro hn hzero_coeff
        have hprevious := hinduction (lt_trans (Nat.lt_succ_self n) hn)
        have hrelation := hcoefficients n
        rw [hzero_coeff, mul_zero] at hrelation
        have hfactor : (n : ℚ) - 2 * index ≠ 0 := by
          have hnq : (n : ℚ) < index := by exact_mod_cast (lt_trans (Nat.lt_succ_self n) hn)
          have hiq : (0 : ℚ) < index := by exact_mod_cast hindex
          linarith
        exact hprevious ((mul_eq_zero.mp hrelation.symm).resolve_left hfactor)
  have hprevious := hnonzero (index - 1) (Nat.sub_lt hindex (by decide))
  have hrelation := hcoefficients (index - 1)
  have hsuccessor : index - 1 + 1 = index := Nat.sub_add_cancel hindex
  rw [hsuccessor, sub_self, zero_mul] at hrelation
  have hfactor : ((index - 1 : ℕ) : ℚ) - 2 * index ≠ 0 := by
    have hlt : ((index - 1 : ℕ) : ℚ) < index := by
      exact_mod_cast (Nat.sub_lt hindex (by decide))
    have hiq : (0 : ℚ) < index := by exact_mod_cast hindex
    linarith
  exact hprevious ((mul_eq_zero.mp hrelation.symm).resolve_left hfactor)

/-- An integral constant multiplier at every nontrivial fixed point is impossible.
Unlike the argument using the pivotal bound, this does not require identifying
the reliability degree with the number of edges. -/
theorem integer_constant_multiplier_impossible
    (reliability fixedPoint : ℚ[X]) (multiplier : ℕ) (hmultiplier : 1 < multiplier)
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ reliability.natDegree)
    (hzero : reliability.derivative.eval 0 = 0)
    (hone : reliability.derivative.eval 1 = 0) :
    ¬ fixedPoint ∣ reliability.derivative - C (multiplier : ℚ) := by
  intro hdivides
  have hquotient := constant_multiplier_polynomial_identity reliability fixedPoint
    (multiplier : ℚ) hfactor hdegree hzero hone
    (by exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hmultiplier))) hdivides
  have hderivative := fixedPoint_derivative_identity reliability fixedPoint hfactor
  apply polynomial_integer_multiplier_obstruction fixedPoint (multiplier - 1)
    (Nat.sub_pos_of_lt hmultiplier) (fixedPoint_eval_zero reliability fixedPoint hfactor hzero)
  rw [Nat.cast_sub (Nat.le_of_lt hmultiplier), Nat.cast_one, map_sub, map_one]
  linear_combination hquotient - hderivative

theorem irreducible_dvd_of_common_root (polynomial target : ℚ[X]) (root : ℝ)
    (hirreducible : Irreducible polynomial) (hroot : aeval root polynomial = 0)
    (htarget : aeval root target = 0) : polynomial ∣ target := by
  have hdivides : polynomial ∣ minpoly ℚ root :=
    ⟨C polynomial.leadingCoeff⁻¹, (minpoly.eq_of_irreducible hirreducible hroot).symm⟩
  exact hdivides.trans (minpoly.dvd ℚ root htarget)

/-- Irreducibility turns one integral multiplier into the impossible constant
multiplier at all roots of the complete fixed-point quotient. -/
theorem irreducible_fixedPoint_derivative_ne_integer
    (reliability fixedPoint : ℚ[X]) (root : ℝ)
    (hirreducible : Irreducible fixedPoint) (hroot : aeval root fixedPoint = 0)
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ reliability.natDegree)
    (hzero : reliability.derivative.eval 0 = 0)
    (hone : reliability.derivative.eval 1 = 0)
    (multiplier : ℕ) (hmultiplier : 1 < multiplier) :
    aeval root reliability.derivative ≠ (multiplier : ℝ) := by
  intro hequal
  apply integer_constant_multiplier_impossible reliability fixedPoint multiplier hmultiplier
    hfactor hdegree hzero hone
  apply irreducible_dvd_of_common_root fixedPoint _ root hirreducible hroot
  simp only [map_sub, aeval_C, hequal]
  norm_num

end Universality.Section4

#print axioms Universality.Section4.polynomial_integer_multiplier_obstruction
#print axioms Universality.Section4.irreducible_fixedPoint_derivative_ne_integer
