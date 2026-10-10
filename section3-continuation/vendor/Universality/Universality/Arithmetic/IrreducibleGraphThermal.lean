import Universality.Arithmetic.IrreducibleThermal
import Universality.Arithmetic.GraphFixedPointCoefficients

/-!
Graph-facing intermediate thermal lemmas. Their explicit reduction hypotheses
are discharged by the final theorem in IrreducibleCommensurability.lean.
-/

namespace Universality.Rule

open Polynomial FiniteNetwork

theorem Classical.irreducible_thermal_no_integer_power_of_nonconstant {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hirreducible : Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ)))
    (hnonconstant : ∀ prime : ℕ, prime.Prime →
      ((rule.network.integerFixedPointPolynomial (h.connected _)).map
        (Int.castRingHom (ZMod prime))).natDegree ≠ 0)
    (exponent : ℕ) (hexponent : 0 < exponent) (integerValue : ℤ) :
    (deriv rule.network.reliability p) ^ exponent ≠ integerValue := by
  have hresponse : aeval p
      (rule.network.integerReliabilityPolynomial.map (Int.castRingHom ℚ)).derivative =
        deriv rule.network.reliability p := by
    rw [rule.network.integerReliabilityPolynomial_map]
    exact (rule.network.hasDerivAt_reliability p).deriv.symm
  rw [← hresponse]
  apply Section4.irreducible_fixedPoint_no_integer_power
    rule.network.integerReliabilityPolynomial
    (rule.network.integerFixedPointPolynomial (h.connected _)) p
    (rule.network.integerFixedPointPolynomial_isPrimitive (h.connected _) h.scale)
    hirreducible ?_ (rule.network.integerFixedPointPolynomial_factor (h.connected _))
    ?_ ?_ ?_ ?_ hnonconstant exponent hexponent integerValue
  · have hroot := rule.network.integerFixedPointPolynomial_root (h.connected _) p hp hp' hfixed
    have hmaps : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = algebraMap ℤ ℝ :=
      Subsingleton.elim _ _
    simpa only [aeval_def, eval₂_map, hmaps] using hroot
  · rw [rule.network.integerReliabilityPolynomial_map]
    exact rule.network.reliabilityPolynomial_natDegree_ge_two (h.connected _) h.scale
  · rw [derivative_map, eval_zero_map,
      rule.network.integerReliabilityPolynomial_derivative_zero h.scale, map_zero]
  · rw [derivative_map, eval_one_map,
      rule.network.integerReliabilityPolynomial_derivative_one h.cut, map_zero]
  · rw [hresponse]
    exact rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale

theorem Classical.irreducible_thermal_no_integer_power_of_mod_two {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hirreducible : Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ)))
    (hmodTwo : ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom (ZMod 2))).natDegree ≠ 0)
    (exponent : ℕ) (hexponent : 0 < exponent) (integerValue : ℤ) :
    (deriv rule.network.reliability p) ^ exponent ≠ integerValue := by
  apply h.irreducible_thermal_no_integer_power_of_nonconstant p hp hp' hfixed hirreducible
    (fun prime hprime => rule.network.integerFixedPointPolynomial_mod_prime_nonconstant_of_mod_two
      (h.connected _) h.scale h.cut hmodTwo prime hprime) exponent hexponent integerValue

end Universality.Rule

#print axioms Universality.Rule.Classical.irreducible_thermal_no_integer_power_of_nonconstant

#print axioms Universality.Rule.Classical.irreducible_thermal_no_integer_power_of_mod_two




