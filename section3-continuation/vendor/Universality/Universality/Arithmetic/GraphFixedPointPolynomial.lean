import Universality.Arithmetic.GraphAlgebraicity
import Universality.Arithmetic.IntegerMultiplierObstruction
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.Content

namespace Universality.FiniteNetwork

open Polynomial

variable {vertices edges : ℕ} (network : FiniteNetwork vertices edges)

/-- The actual finite Bernoulli configuration sum, with integer coefficients. -/
noncomputable def integerReliabilityPolynomial : ℤ[X] :=
  ∑ configuration : Configuration edges,
    if network.crosses configuration then
      ∏ edge : Fin edges, if configuration edge then X else 1 - X else 0

theorem integerReliabilityPolynomial_map :
    network.integerReliabilityPolynomial.map (Int.castRingHom ℚ) =
      network.reliabilityPolynomial := by
  simp [integerReliabilityPolynomial, reliabilityPolynomial, Polynomial.map_sum,
    Polynomial.map_prod, apply_ite]

theorem integerReliabilityPolynomial_eval (p : ℝ) :
    aeval p network.integerReliabilityPolynomial = network.reliability p := by
  rw [← network.reliabilityPolynomial_eval, ← network.integerReliabilityPolynomial_map]
  simp only [eval₂_map, aeval_def]
  rfl

theorem integerReliabilityPolynomial_derivative_eval (p : ℝ) :
    aeval p network.integerReliabilityPolynomial.derivative = deriv network.reliability p := by
  rw [(network.hasDerivAt_reliability p).deriv, ← network.integerReliabilityPolynomial_map,
    Polynomial.derivative_map, Polynomial.eval₂_map]
  rfl

theorem integerReliabilityPolynomial_derivative_zero
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    network.integerReliabilityPolynomial.derivative.eval 0 = 0 := by
  apply Int.cast_injective (α := ℝ)
  have h := network.integerReliabilityPolynomial_derivative_eval 0
  rw [network.derivative_zero_zero hscale] at h
  simpa [aeval_def, ← eval₂_at_apply, ← coeff_zero_eq_eval_zero] using h

theorem integerReliabilityPolynomial_derivative_one
    (hcut : ∀ edge, network.crosses (onlyClosed edge) = true) :
    network.integerReliabilityPolynomial.derivative.eval 1 = 0 := by
  apply Int.cast_injective (α := ℝ)
  have h := network.integerReliabilityPolynomial_derivative_eval 1
  rw [network.derivative_one_zero hcut] at h
  simpa [aeval_def, ← eval₂_at_apply] using h

theorem integerReliabilityPolynomial_zero : network.integerReliabilityPolynomial.eval 0 = 0 := by
  apply Int.cast_injective (α := ℝ)
  have h := network.integerReliabilityPolynomial_eval 0
  rw [network.reliability_zero] at h
  simpa [aeval_def, ← eval₂_at_apply, ← coeff_zero_eq_eval_zero] using h

theorem integerReliabilityPolynomial_one
    (hconnected : network.fullGraph.Reachable network.source network.target) :
    network.integerReliabilityPolynomial.eval 1 = 1 := by
  apply Int.cast_injective (α := ℝ)
  have h := network.integerReliabilityPolynomial_eval 1
  rw [network.reliability_one hconnected] at h
  simpa [aeval_def, ← eval₂_at_apply] using h

theorem integerReliabilityPolynomial_natDegree_ge_two
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    2 ≤ network.integerReliabilityPolynomial.natDegree := by
  by_contra hdegree
  have hform := eq_X_add_C_of_natDegree_le_one (show network.integerReliabilityPolynomial.natDegree ≤ 1 by omega)
  have hzero := network.integerReliabilityPolynomial_zero
  have hone := network.integerReliabilityPolynomial_one hconnected
  have hderivative := network.integerReliabilityPolynomial_derivative_zero hscale
  rw [hform] at hzero hone hderivative
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add] at hzero
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_one] at hone
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
    zero_mul, one_mul, mul_one, add_zero, zero_add, eval_C] at hderivative
  omega

theorem reliabilityPolynomial_natDegree_ge_two
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    2 ≤ network.reliabilityPolynomial.natDegree := by
  rw [← network.integerReliabilityPolynomial_map, natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ))]
  exact network.integerReliabilityPolynomial_natDegree_ge_two hconnected hscale

theorem exists_integer_fixedPoint_polynomial
    (hconnected : network.fullGraph.Reachable network.source network.target) :
    ∃ fixedPoint : ℤ[X], network.integerReliabilityPolynomial - X =
      X * (1 - X) * fixedPoint := by
  have hzero : (network.integerReliabilityPolynomial - X).eval 0 = 0 := by
    apply Int.cast_injective (α := ℝ)
    have h := network.integerReliabilityPolynomial_eval 0
    rw [network.reliability_zero] at h
    simpa [eval_sub, aeval_def, ← eval₂_at_apply, ← coeff_zero_eq_eval_zero] using h
  have hone : (network.integerReliabilityPolynomial - X).eval 1 = 0 := by
    apply Int.cast_injective (α := ℝ)
    have h := network.integerReliabilityPolynomial_eval 1
    rw [network.reliability_one hconnected] at h
    simpa [eval_sub, aeval_def, ← eval₂_at_apply] using sub_eq_zero.mpr h
  have hdivides : X ∣ network.integerReliabilityPolynomial - X :=
    X_dvd_iff.mpr (by simpa only [coeff_zero_eq_eval_zero] using hzero)
  obtain ⟨quotient, hquotient⟩ := hdivides
  have hquotient_one : quotient.eval 1 = 0 := by
    rw [hquotient, eval_mul, eval_X, one_mul] at hone
    exact hone
  obtain ⟨fixedPoint, hfixedPoint⟩ :=
    (dvd_iff_isRoot.mpr (show IsRoot quotient (1 : ℤ) from hquotient_one) : X - C (1 : ℤ) ∣ quotient)
  refine ⟨-fixedPoint, ?_⟩
  rw [hquotient, hfixedPoint]
  simp only [map_one]
  ring

/-- The complete fixed-point quotient after removing the two trivial roots.
The existence of the integer factor has already been proved from the graph. -/
noncomputable def integerFixedPointPolynomial
    (hconnected : network.fullGraph.Reachable network.source network.target) : ℤ[X] :=
  Classical.choose (network.exists_integer_fixedPoint_polynomial hconnected)

theorem integerFixedPointPolynomial_factor
    (hconnected : network.fullGraph.Reachable network.source network.target) :
    network.integerReliabilityPolynomial - X =
      X * (1 - X) * network.integerFixedPointPolynomial hconnected :=
  Classical.choose_spec (network.exists_integer_fixedPoint_polynomial hconnected)

theorem integerFixedPointPolynomial_zero
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    (network.integerFixedPointPolynomial hconnected).eval 0 = -1 :=
  Section4.fixedPoint_eval_zero _ _ (network.integerFixedPointPolynomial_factor hconnected)
    (network.integerReliabilityPolynomial_derivative_zero hscale)

theorem integerFixedPointPolynomial_one
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hcut : ∀ edge, network.crosses (onlyClosed edge) = true) :
    (network.integerFixedPointPolynomial hconnected).eval 1 = 1 :=
  Section4.fixedPoint_eval_one _ _ (network.integerFixedPointPolynomial_factor hconnected)
    (network.integerReliabilityPolynomial_derivative_one hcut)

theorem integerFixedPointPolynomial_isPrimitive
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    (network.integerFixedPointPolynomial hconnected).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro coefficient hdivides
  have hdivides_neg_one : coefficient ∣ (-1 : ℤ) := by
    obtain ⟨quotient, hquotient⟩ := hdivides
    refine ⟨quotient.eval 0, ?_⟩
    rw [← network.integerFixedPointPolynomial_zero hconnected hscale, hquotient,
      eval_mul, eval_C]
  exact isUnit_of_dvd_unit hdivides_neg_one (by simp)

theorem rationalFixedPointPolynomial_factor
    (hconnected : network.fullGraph.Reachable network.source network.target) :
    network.reliabilityPolynomial - X = X * (1 - X) *
      (network.integerFixedPointPolynomial hconnected).map (Int.castRingHom ℚ) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (network.integerFixedPointPolynomial_factor hconnected)
  simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_mul,
    Polynomial.map_one, network.integerReliabilityPolynomial_map] using h

theorem integerFixedPointPolynomial_root
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : network.reliability p = p) :
    aeval p (network.integerFixedPointPolynomial hconnected) = 0 := by
  have h := congrArg (aeval p) (network.integerFixedPointPolynomial_factor hconnected)
  rw [map_sub, network.integerReliabilityPolynomial_eval, hfixed,
    aeval_X, sub_self, map_mul, map_mul, aeval_X, map_sub, aeval_one, aeval_X] at h
  exact (mul_eq_zero.mp h.symm).resolve_left
    (mul_ne_zero (ne_of_gt hp) (ne_of_gt (sub_pos.mpr hp')))

end Universality.FiniteNetwork

#print axioms Universality.FiniteNetwork.integerFixedPointPolynomial_factor
#print axioms Universality.FiniteNetwork.integerFixedPointPolynomial_isPrimitive
