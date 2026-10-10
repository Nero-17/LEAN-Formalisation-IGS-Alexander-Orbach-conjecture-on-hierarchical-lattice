import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact algebra for the five-cycle example

The two terminal paths have lengths two and three.  This file verifies the
polynomial identities and rational inequalities used in the example.  It does
not formalize Bernoulli percolation, a random recursive eigenlaw, or a moment
estimate.  In the final theorem the inverse-moment estimate is an explicit
assumption, so the conclusion about the scaling factor is conditional.
-/

set_option autoImplicit false

namespace IGSIII.Chemical.FiveCycle

/-- The reliability polynomial for two edge-disjoint paths of lengths two
and three.  Its identification with a probability is not asserted here. -/
def reliability (q : ℝ) : ℝ := q ^ 2 + q ^ 3 - q ^ 5

theorem reliability_eq_complement_product (q : ℝ) :
    reliability q = 1 - (1 - q ^ 2) * (1 - q ^ 3) := by
  unfold reliability
  ring

theorem reliability_sub_self_factorization (q : ℝ) :
    reliability q - q = q * (1 - q) * (q ^ 3 + q ^ 2 - 1) := by
  unfold reliability
  ring

theorem reliability_fixedPoint_of_criticalEquation {q : ℝ}
    (criticalEquation : q ^ 3 + q ^ 2 = 1) :
    reliability q = q := by
  have factorization := reliability_sub_self_factorization q
  rw [criticalEquation] at factorization
  have zeroDifference : reliability q - q = 0 := by
    simpa only [sub_self, mul_zero] using factorization
  exact sub_eq_zero.mp zeroDifference

theorem criticalEquation_of_nonendpoint_fixedPoint {q : ℝ}
    (nonzero : q ≠ 0) (notOne : q ≠ 1)
    (fixedPoint : reliability q = q) :
    q ^ 3 + q ^ 2 = 1 := by
  have factorization := reliability_sub_self_factorization q
  rw [fixedPoint, sub_self] at factorization
  have nonzeroFactors : q * (1 - q) ≠ 0 :=
    mul_ne_zero nonzero (sub_ne_zero.mpr notOne.symm)
  have zeroCriticalFactor : q ^ 3 + q ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp factorization.symm).resolve_left nonzeroFactors
  linarith

theorem nonendpoint_fixedPoint_iff {q : ℝ}
    (nonzero : q ≠ 0) (notOne : q ≠ 1) :
    reliability q = q ↔ q ^ 3 + q ^ 2 = 1 := by
  constructor
  · exact criticalEquation_of_nonendpoint_fixedPoint nonzero notOne
  · exact reliability_fixedPoint_of_criticalEquation

/-- The upper bound follows from the equation alone. -/
theorem critical_root_lt_four_fifths {q : ℝ}
    (criticalEquation : q ^ 3 + q ^ 2 = 1) :
    q < (4 : ℝ) / 5 := by
  by_contra notBelow
  have lowerBound : (4 : ℝ) / 5 ≤ q := le_of_not_gt notBelow
  have squareLowerBound : (16 : ℝ) / 25 ≤ q ^ 2 := by
    nlinarith [sq_nonneg (q - (4 : ℝ) / 5)]
  nlinarith [mul_nonneg (sub_nonneg.mpr lowerBound) (sq_nonneg q)]

/-- All bounds are exact rational inequalities; no decimal approximation is
used.  The hypothesis `q < 1` is unnecessary for this conclusion. -/
theorem inverse_third_moment_coefficient_bounds {q : ℝ}
    (positive : 0 < q) (criticalEquation : q ^ 3 + q ^ 2 = 1) :
    0 < q / 8 + q ^ 2 / 27 ∧
      q / 8 + q ^ 2 / 27 < (167 : ℝ) / 1350 ∧
      (167 : ℝ) / 1350 < 1 / 8 := by
  have upperBound := critical_root_lt_four_fifths criticalEquation
  have squareUpperBound : q ^ 2 < (16 : ℝ) / 25 := by
    nlinarith [mul_pos positive (sub_pos.mpr upperBound)]
  constructor
  · positivity
  constructor
  · nlinarith
  · norm_num

/-- Conditional algebraic consequence of the stated inverse-moment bound.
This theorem does not establish that bound for any random variable or process. -/
theorem scaling_factor_gt_two_of_inverse_moment_bound {q scaling : ℝ}
    (positive : 0 < q) (criticalEquation : q ^ 3 + q ^ 2 = 1)
    (positiveScaling : 0 < scaling)
    (inverseMomentBound : 1 ≤ (q / 8 + q ^ 2 / 27) * scaling ^ 3) :
    2 < scaling := by
  obtain ⟨positiveCoefficient, coefficientBound, rationalBound⟩ :=
    inverse_third_moment_coefficient_bounds positive criticalEquation
  have coefficientBelowEighth : q / 8 + q ^ 2 / 27 < 1 / 8 :=
    lt_trans coefficientBound rationalBound
  by_contra notAbove
  have scalingUpperBound : scaling ≤ 2 := le_of_not_gt notAbove
  have squareUpperBound : scaling ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg positiveScaling.le
      (sub_nonneg.mpr scalingUpperBound)]
  have cubeUpperBound : scaling ^ 3 ≤ 8 := by
    nlinarith [mul_nonneg (sq_nonneg scaling)
      (sub_nonneg.mpr scalingUpperBound)]
  have productUpperBound :=
    mul_le_mul_of_nonneg_left cubeUpperBound positiveCoefficient.le
  nlinarith

end IGSIII.Chemical.FiveCycle

