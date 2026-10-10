import Universality.Arithmetic.IrreducibleCommensurability

/-!
The closing unnumbered corollary of Section 4: a rational pivotal dimension
precludes irreducibility of the complete fixed-point quotient. The proof uses
only the integer-power obstruction and elementary logarithm identities; neither
Gelfond–Schneider nor Six Exponentials enters its axiom dependency list.
-/

namespace Universality.Rule

noncomputable section
open Polynomial FiniteNetwork

theorem Classical.irreducible_pivotal_dimension_irrational {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hirreducible : Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ))) :
    Irrational (rule.criticalDimensions p 2) := by
  apply Section4.logarithmic_dimension_irrational_of_no_integer_power
    (rule.network.fullGraph.dist rule.network.source rule.network.target)
    (deriv rule.network.reliability p) h.scale
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale)
  exact h.irreducible_thermal_no_integer_power p hp hp' hfixed hirreducible

/-- Rationality of the actual pivotal dimension obstructs irreducibility of
its complete fixed-point quotient, before any mass nonsplitting hypothesis. -/
theorem Classical.not_irreducible_fixedPoint_of_rational_pivotal_dimension {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hrational : ∃ dimension : ℚ, (dimension : ℝ) = rule.criticalDimensions p 2) :
    ¬ Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ)) := by
  intro hirreducible
  exact h.irreducible_pivotal_dimension_irrational p hp hp' hfixed hirreducible hrational

theorem Classical.not_irreducible_fixedPoint_of_pivotal_dimension_mem_rat {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hrational : rule.criticalDimensions p 2 ∈ Set.range (fun dimension : ℚ => (dimension : ℝ))) :
    ¬ Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ)) :=
  h.not_irreducible_fixedPoint_of_rational_pivotal_dimension p hp hp' hfixed hrational

end
end Universality.Rule

#print axioms Universality.Rule.Classical.irreducible_pivotal_dimension_irrational
#print axioms Universality.Rule.Classical.not_irreducible_fixedPoint_of_rational_pivotal_dimension
#print axioms Universality.Rule.Classical.not_irreducible_fixedPoint_of_pivotal_dimension_mem_rat
