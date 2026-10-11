import Universality.Arithmetic.GraphFixedPointStructure
import Universality.Arithmetic.IrreducibleGraphThermal
import Universality.Arithmetic.GraphLogarithmicIndependence
import Universality.Arithmetic.GraphDimensionRank

/-!
The complete irreducibility criterion of Section 4 for actual classical graph
rules. All polynomial and characteristic-two structure is derived from the
actual graph. Irreducibility and mass nonsplitting are exactly the manuscript's
arithmetic hypotheses. Only the scale conclusion uses six exponentials; only
the transcendence conclusion uses Gelfond--Schneider.
-/

namespace Universality.Rule
noncomputable section
open Polynomial FiniteNetwork Matrix

/-- The actual pivotal multiplier has no positive integer power in the integers. -/
theorem Classical.irreducible_thermal_no_integer_power {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hirreducible : Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ)))
    (exponent : ℕ) (hexponent : 0 < exponent) (integerValue : ℤ) :
    (deriv rule.network.reliability p) ^ exponent ≠ integerValue :=
  h.irreducible_thermal_no_integer_power_of_nonconstant p hp hp' hfixed hirreducible
    h.fixedPointPolynomial_mod_prime_nonconstant exponent hexponent integerValue

theorem Classical.irreducible_pivotal_dimension_transcendental {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hirreducible : Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ))) :
    Transcendental ℚ (rule.criticalDimensions p 2) := by
  apply Section4.logarithmic_dimension_transcendental_of_no_integer_power
    (rule.network.fullGraph.dist rule.network.source rule.network.target)
    (deriv rule.network.reliability p) h.scale
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale)
    (h.critical_responses_algebraic p hfixed).2.1
  exact h.irreducible_thermal_no_integer_power p hp hp' hfixed hirreducible

theorem Classical.irreducible_criticalDimensions_independent {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hirreducible : Irreducible ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ)))
    (hnonsplit : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p}) :
    LinearIndependent ℚ (rule.criticalDimensions p) :=
  h.criticalDimensions_independent_of_nonsplit_mass p hp hp' hfixed
    (h.irreducible_thermal_no_integer_power p hp hp' hfixed hirreducible) hnonsplit

/-- The manuscript's irreducible commensurability theorem, with no extra
reduction, lifting, degree or logarithmic-independence premise. -/
theorem Classical.commensurate_of_irreducible_fixedPoint {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (hequal : first.criticalDimensions p = second.criticalDimensions q)
    (hirreducible : Irreducible ((first.network.integerFixedPointPolynomial (hfirst.connected _)).map
      (Int.castRingHom ℚ)))
    (hnonsplit : (spectralRadius ℂ ((first.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p}) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) :=
  hfirst.commensurate_of_nonsplit_mass hsecond p q hp hp' hq hq' hfixedFirst hfixedSecond hequal
    (hfirst.irreducible_thermal_no_integer_power p hp hp' hfixedFirst hirreducible) hnonsplit

/-- One irreducible nonsplit representative supplies a common primitive base
for every member of an arbitrary family with the same actual growth tuple. -/
theorem Classical.common_primitive_base_of_irreducible_fixedPoint {ι : Type*}
    (rules : ι → Rule) (criticalPoints : ι → ℝ) (reference : ι)
    (hclassical : ∀ index, (rules index).Classical)
    (hpositive : ∀ index, 0 < criticalPoints index)
    (hless : ∀ index, criticalPoints index < 1)
    (hfixed : ∀ index, (rules index).network.reliability (criticalPoints index) = criticalPoints index)
    (hcommon : ∀ index, (rules index).criticalDimensions (criticalPoints index) =
      (rules reference).criticalDimensions (criticalPoints reference))
    (hirreducible : Irreducible (((rules reference).network.integerFixedPointPolynomial
      ((hclassical reference).connected _)).map (Int.castRingHom ℚ)))
    (hnonsplit : (spectralRadius ℂ (((rules reference).network.massMatrix
      (criticalPoints reference)).map Complex.ofReal)).toReal ∉
        IntermediateField.adjoin ℚ {criticalPoints reference}) :
    ∃ base : ℕ, Section4.PrimitiveIntegerBase base ∧
      ∀ index, ∃ exponent : ℕ, 0 < exponent ∧
        (rules index).network.fullGraph.dist
          (rules index).network.source (rules index).network.target = base ^ exponent := by
  letI : Nonempty ι := ⟨reference⟩
  have hreference (index : ι) :=
    (hclassical reference).commensurate_of_irreducible_fixedPoint (hclassical index)
      (criticalPoints reference) (criticalPoints index)
      (hpositive reference) (hless reference) (hpositive index) (hless index)
      (hfixed reference) (hfixed index) (hcommon index).symm hirreducible hnonsplit
  apply Section4.common_primitive_integer_base
    (fun index => (rules index).network.fullGraph.dist
      (rules index).network.source (rules index).network.target)
    (fun index => (hclassical index).scale)
  intro first second
  exact (hreference first).symm.trans (hreference second)
end
end Universality.Rule

#print axioms Universality.Rule.Classical.irreducible_thermal_no_integer_power
#print axioms Universality.Rule.Classical.irreducible_pivotal_dimension_transcendental
#print axioms Universality.Rule.Classical.irreducible_criticalDimensions_independent
#print axioms Universality.Rule.Classical.commensurate_of_irreducible_fixedPoint

#print axioms Universality.Rule.Classical.common_primitive_base_of_irreducible_fixedPoint
