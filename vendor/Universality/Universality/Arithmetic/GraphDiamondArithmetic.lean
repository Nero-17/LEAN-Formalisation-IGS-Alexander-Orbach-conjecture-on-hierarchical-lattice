import Universality.Arithmetic.DiamondArithmetic
import Universality.Arithmetic.GraphLogarithmicIndependence
import Universality.Arithmetic.CommonPrimitiveBase
import Universality.Arithmetic.GraphFixedPointPolynomial
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! The exact diamond certificates discharge all arithmetic premises in the
actual-graph criterion. The final scale theorem has no irreducibility, no-power,
or nonsplitting premise left for the diamond representative. -/

namespace Universality
noncomputable section
open Polynomial

theorem diamond_fixedPoint_expression_irreducible :
    Irreducible (X ^ 2 + X - 1 : ℚ[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdegree : (X ^ 2 + X - 1 : ℚ[X]).natDegree = 2 := by
      compute_degree
      norm_num
    simp only [hdegree, Finset.mem_Icc]
    norm_num
  · intro root hroot
    have hquadratic : root ^ 2 + root - 1 = 0 := by simpa [IsRoot] using hroot
    have hnonsquare : ¬ IsSquare (5 : ℚ) := by norm_num
    exact hnonsquare ⟨2 * root + 1, by nlinarith⟩

theorem diamond_actual_fixedPoint_polynomial :
    (diamondNetwork.integerFixedPointPolynomial
      (diamondRule_classical.connected diamondNetwork.target)).map (Int.castRingHom ℚ) =
      X ^ 2 + X - 1 := by
  have hfactor := diamondNetwork.rationalFixedPointPolynomial_factor
    (diamondRule_classical.connected diamondNetwork.target)
  have hnonzero : (X * (1 - X) : ℚ[X]) ≠ 0 := by
    apply mul_ne_zero X_ne_zero
    intro hzero
    have hcoefficient := congrArg (fun polynomial : ℚ[X] => polynomial.coeff 1) hzero
    norm_num [Polynomial.coeff_one] at hcoefficient
  apply mul_left_cancel₀ hnonzero
  rw [← hfactor, diamond_reliabilityPolynomial]
  ring

theorem diamond_actual_fixedPoint_irreducible :
    Irreducible ((diamondNetwork.integerFixedPointPolynomial
      (diamondRule_classical.connected diamondNetwork.target)).map (Int.castRingHom ℚ)) := by
  rw [diamond_actual_fixedPoint_polynomial]
  exact diamond_fixedPoint_expression_irreducible

theorem diamond_actual_criticalDimensions_independent :
    LinearIndependent ℚ (diamondRule.criticalDimensions diamondCriticalProbability) :=
  diamondRule_classical.criticalDimensions_independent_of_nonsplit_mass
    diamondCriticalProbability diamond_critical_probability_bounds.1
    diamond_critical_probability_bounds.2 diamond_critical_fixed_point
    diamond_actual_pivotal_no_integer_power diamond_actual_mass_nonsplit

theorem Rule.Classical.scale_power_two_of_diamond_dimensions {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hequal : rule.criticalDimensions p = diamondRule.criticalDimensions diamondCriticalProbability) :
    ∃ exponent : ℕ, 0 < exponent ∧
      rule.network.fullGraph.dist rule.network.source rule.network.target = 2 ^ exponent := by
  have hcommensurate := diamondRule_classical.commensurate_of_nonsplit_mass h
    diamondCriticalProbability p diamond_critical_probability_bounds.1
    diamond_critical_probability_bounds.2 hp hp' diamond_critical_fixed_point hfixed hequal.symm
    diamond_actual_pivotal_no_integer_power diamond_actual_mass_nonsplit
  change ScaleCommensurate
    (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target)
    (rule.network.fullGraph.dist rule.network.source rule.network.target) at hcommensurate
  rw [diamond_terminal_distance] at hcommensurate
  apply (Section4.commensurate_with_primitive_base_iff (base := 2) ?_ h.scale).mp hcommensurate
  refine ⟨by norm_num, ?_⟩
  intro root exponent hexponent hpower
  have hpow := Nat.Prime.pow_eq_iff Nat.prime_two |>.mp hpower.symm
  omega

end
end Universality

#print axioms Universality.diamond_actual_criticalDimensions_independent
#print axioms Universality.Rule.Classical.scale_power_two_of_diamond_dimensions
#print axioms Universality.diamond_actual_fixedPoint_irreducible
