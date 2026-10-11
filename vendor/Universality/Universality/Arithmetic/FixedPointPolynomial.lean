import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Algebraic consequences of the fixed-point factorisation in Section 4.

The hypotheses below are polynomial identities. These lemmas do not assert the
graph-theoretic degree or parity arguments: those are separate obligations.
-/

namespace Universality.Section4

open Polynomial

section CommRing

variable {R : Type*} [CommRing R]

theorem fixedPoint_derivative_identity (reliability fixedPoint : R[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint) :
    reliability.derivative = 1 + (1 - 2 * X) * fixedPoint +
      X * (1 - X) * fixedPoint.derivative := by
  have hd := congrArg Polynomial.derivative hfactor
  simp only [derivative_sub, derivative_X, derivative_mul, derivative_one] at hd
  linear_combination hd

theorem fixedPoint_eval_zero (reliability fixedPoint : R[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hderivative : reliability.derivative.eval 0 = 0) : fixedPoint.eval 0 = -1 := by
  have hd := congrArg (Polynomial.eval 0)
    (fixedPoint_derivative_identity reliability fixedPoint hfactor)
  simp only [eval_add, eval_one, eval_mul, eval_sub, eval_X, eval_ofNat,
    mul_zero, sub_zero, one_mul, zero_mul, add_zero, hderivative] at hd
  linear_combination -hd

theorem fixedPoint_eval_one (reliability fixedPoint : R[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hderivative : reliability.derivative.eval 1 = 0) : fixedPoint.eval 1 = 1 := by
  have hd := congrArg (Polynomial.eval 1)
    (fixedPoint_derivative_identity reliability fixedPoint hfactor)
  simp only [eval_add, eval_one, eval_mul, eval_sub, eval_X, eval_ofNat,
    mul_one, sub_self, mul_zero, zero_mul, add_zero, hderivative] at hd
  linear_combination hd

theorem fixedPoint_simple_root_identity (reliability fixedPoint : R[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint) (root : R)
    (hroot : fixedPoint.eval root = 0)
    (hderivative : reliability.derivative.eval root = 0) :
    root * (1 - root) * fixedPoint.derivative.eval root = -1 := by
  have hd := congrArg (Polynomial.eval root)
    (fixedPoint_derivative_identity reliability fixedPoint hfactor)
  simp only [eval_add, eval_one, eval_mul, eval_sub, eval_X, eval_ofNat,
    hroot, mul_zero, add_zero, hderivative] at hd
  linear_combination -hd

end CommRing

section Field

variable {K : Type*} [Field K]

theorem fixedPoint_derivative_ne_zero_at_root (reliability fixedPoint : K[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint) (root : K)
    (hroot : fixedPoint.eval root = 0)
    (hderivative : reliability.derivative.eval root = 0) :
    fixedPoint.derivative.eval root ≠ 0 := by
  intro hzero
  have hd := fixedPoint_simple_root_identity reliability fixedPoint hfactor root
    hroot hderivative
  simp only [hzero, mul_zero, eq_neg_iff_add_eq_zero, zero_add] at hd
  exact one_ne_zero hd

theorem fixedPoint_natDegree (reliability fixedPoint : K[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ reliability.natDegree) (hfixedPoint : fixedPoint ≠ 0) :
    fixedPoint.natDegree + 2 = reliability.natDegree := by
  have hone : (1 - X : K[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    norm_num at this
  have hquadratic : (X * (1 - X) : K[X]).natDegree = 2 := by
    rw [natDegree_mul X_ne_zero hone, natDegree_X,
      natDegree_sub_eq_right_of_natDegree_lt (by simp)]
    norm_num
  have hd := congrArg Polynomial.natDegree hfactor
  rw [natDegree_sub_eq_left_of_natDegree_lt (by simp only [natDegree_X]; omega),
    natDegree_mul (mul_ne_zero X_ne_zero hone) hfixedPoint, hquadratic] at hd
  omega

theorem fixedPoint_leadingCoeff (reliability fixedPoint : K[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ reliability.natDegree) :
    reliability.leadingCoeff = -fixedPoint.leadingCoeff := by
  have hd := congrArg Polynomial.leadingCoeff hfactor
  rw [leadingCoeff_sub_of_degree_lt (degree_lt_degree (by simp only [natDegree_X]; omega)),
    leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_X,
    leadingCoeff_sub_of_degree_lt' (by simp), leadingCoeff_X] at hd
  simpa using hd

end Field

theorem constant_multiplier_polynomial_identity
    (reliability fixedPoint : ℚ[X]) (multiplier : ℚ)
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ reliability.natDegree)
    (hzero : reliability.derivative.eval 0 = 0)
    (hone : reliability.derivative.eval 1 = 0)
    (hmultiplier : multiplier ≠ 0)
    (hdivides : fixedPoint ∣ reliability.derivative - C multiplier) :
    reliability.derivative - C multiplier =
      fixedPoint * (C multiplier * (1 - 2 * X)) := by
  have hfixedZero := fixedPoint_eval_zero reliability fixedPoint hfactor hzero
  have hfixedOne := fixedPoint_eval_one reliability fixedPoint hfactor hone
  have hfixedPoint : fixedPoint ≠ 0 := by
    intro h
    simp [h] at hfixedZero
  obtain ⟨quotient, hquotient⟩ := hdivides
  have hquotientZero := congrArg (Polynomial.eval 0) hquotient
  simp only [eval_sub, eval_C, eval_mul, hzero, hfixedZero] at hquotientZero
  have hquotientOne := congrArg (Polynomial.eval 1) hquotient
  simp only [eval_sub, eval_C, eval_mul, hone, hfixedOne] at hquotientOne
  have hquotientNonzero : quotient ≠ 0 := by
    intro h
    simp [h] at hquotientZero
    exact hmultiplier hquotientZero
  have hquotientDegree := congrArg Polynomial.natDegree hquotient
  rw [natDegree_sub_C, natDegree_derivative,
    natDegree_mul hfixedPoint hquotientNonzero] at hquotientDegree
  have hfixedDegree := fixedPoint_natDegree reliability fixedPoint hfactor hdegree hfixedPoint
  have hquotientLinear : quotient.natDegree = 1 := by omega
  have hquotientForm := eq_X_add_C_of_natDegree_le_one (le_of_eq hquotientLinear)
  rw [hquotientForm] at hquotientZero hquotientOne
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add,
    mul_one] at hquotientZero hquotientOne
  have hlinear : quotient.coeff 1 = -2 * multiplier := by linarith
  have hconstant : quotient.coeff 0 = multiplier := by linarith
  rw [hquotient, hquotientForm, hlinear, hconstant]
  simp only [map_mul, map_neg, map_ofNat]
  ring

/-- The constant-multiplier step of the irreducibility criterion. The quotient
is linear; its endpoint values and leading coefficient force twice the
multiplier to equal the degree. No root enumeration or residue theorem enters.
-/
theorem constant_multiplier_twice_eq_degree
    (reliability fixedPoint : ℚ[X]) (multiplier : ℚ)
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ reliability.natDegree)
    (hzero : reliability.derivative.eval 0 = 0)
    (hone : reliability.derivative.eval 1 = 0)
    (hmultiplier : multiplier ≠ 0)
    (hdivides : fixedPoint ∣ reliability.derivative - C multiplier) :
    2 * multiplier = (reliability.natDegree : ℚ) := by
  have hfixedZero := fixedPoint_eval_zero reliability fixedPoint hfactor hzero
  have hfixedOne := fixedPoint_eval_one reliability fixedPoint hfactor hone
  have hfixedPoint : fixedPoint ≠ 0 := by
    intro h
    simp [h] at hfixedZero
  obtain ⟨quotient, hquotient⟩ := hdivides
  have hquotientZero := congrArg (Polynomial.eval 0) hquotient
  simp only [eval_sub, eval_C, eval_mul, hzero, hfixedZero] at hquotientZero
  have hquotientOne := congrArg (Polynomial.eval 1) hquotient
  simp only [eval_sub, eval_C, eval_mul, hone, hfixedOne] at hquotientOne
  have hquotientNonzero : quotient ≠ 0 := by
    intro h
    simp [h] at hquotientZero
    exact hmultiplier hquotientZero
  have hquotientDegree := congrArg Polynomial.natDegree hquotient
  rw [natDegree_sub_C, natDegree_derivative,
    natDegree_mul hfixedPoint hquotientNonzero] at hquotientDegree
  have hfixedDegree := fixedPoint_natDegree reliability fixedPoint hfactor hdegree hfixedPoint
  have hquotientLinear : quotient.natDegree = 1 := by omega
  have hquotientForm := eq_X_add_C_of_natDegree_le_one (le_of_eq hquotientLinear)
  rw [hquotientForm] at hquotientZero hquotientOne
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add,
    mul_one] at hquotientZero hquotientOne
  have hlinear : quotient.coeff 1 = -2 * multiplier := by
    linarith
  have hleading := congrArg Polynomial.leadingCoeff hquotient
  rw [leadingCoeff_sub_of_degree_lt (degree_lt_degree (by
      simp only [natDegree_C, natDegree_derivative]
      omega)), leadingCoeff_derivative, leadingCoeff_mul,
    fixedPoint_leadingCoeff reliability fixedPoint hfactor hdegree] at hleading
  have hquotientLeading : quotient.leadingCoeff = quotient.coeff 1 := by
    rw [Polynomial.leadingCoeff, hquotientLinear]
  rw [hquotientLeading, hlinear] at hleading
  have hfixedLeading : fixedPoint.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfixedPoint
  apply (mul_right_inj' hfixedLeading).mp
  linear_combination hleading

/-- The sharp pivotal-response bound rules out a nonzero constant multiplier
when the reliability polynomial has degree at least four. -/
theorem constant_multiplier_impossible
    (reliability fixedPoint : ℚ[X]) (multiplier : ℚ)
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 4 ≤ reliability.natDegree)
    (hzero : reliability.derivative.eval 0 = 0)
    (hone : reliability.derivative.eval 1 = 0)
    (hmultiplier : multiplier ≠ 0)
    (hbound : multiplier ^ 2 < (reliability.natDegree : ℚ)) :
    ¬ fixedPoint ∣ reliability.derivative - C multiplier := by
  intro hdivides
  have hconstant := constant_multiplier_twice_eq_degree reliability fixedPoint multiplier
    hfactor (by omega) hzero hone hmultiplier hdivides
  have hdegree' : (4 : ℚ) ≤ reliability.natDegree := by exact_mod_cast hdegree
  nlinarith [sq_nonneg (multiplier - 2)]

/-- The endpoint values isolate characteristic two as the only possible
constant reduction. The remaining characteristic-two obstruction is genuinely
graph-theoretic and is not asserted here. -/
theorem fixedPoint_constant_reduction_forces_two_zero
    {K : Type*} [Field K] (fixedPoint : K[X])
    (hzero : fixedPoint.eval 0 = -1) (hone : fixedPoint.eval 1 = 1)
    (hconstant : fixedPoint.natDegree = 0) : (2 : K) = 0 := by
  have hform := eq_C_of_natDegree_eq_zero hconstant
  rw [hform] at hzero hone
  simp only [eval_C] at hzero hone
  linear_combination hzero - hone

end Universality.Section4
