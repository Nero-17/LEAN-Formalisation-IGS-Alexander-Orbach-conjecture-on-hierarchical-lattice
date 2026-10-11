import Universality.Arithmetic.LogarithmicIndependence
import Universality.Arithmetic.IrreducibleMass
import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Arithmetic.DimensionRank
import Universality.Percolation.PivotalResponseBound

/-!
# Independence and scale rigidity for the actual graph dimensions

The substantive arithmetic hypotheses are absence of positive integer powers
of the pivotal multiplier and nonsplitting of the actual mass spectral radius
over the actual critical field. No dimension-independence premise is assumed.
-/

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix

theorem Classical.criticalDimensions_independent_of_nonsplit_mass
    {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hno_integer_power : ∀ exponent : ℕ, 0 < exponent →
      ∀ integer : ℤ, deriv rule.network.reliability p ^ exponent ≠ integer)
    (hnonsplit : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p}) :
    LinearIndependent ℚ (rule.criticalDimensions p) := by
  have hresponse := rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale
  have hsquare := rule.network.pivotal_response_sq_lt_edges p hp hp' hfixed h.scale
  have hedges : 1 < rule.edges := by
    have hreal : (1 : ℝ) < rule.edges := by nlinarith
    exact_mod_cast hreal
  exact Section4.logarithmic_dimensions_independent_of_mass_power_not_mem
    (IntermediateField.adjoin ℚ {p}).toSubfield rule.edges
    (rule.network.fullGraph.dist rule.network.source rule.network.target)
    (deriv rule.network.reliability p)
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    hedges h.scale hresponse (h.mass_spectralRadius_positive_eigenvector p hp hp').1
    (rule.network.reliability_deriv_mem_adjoin p) hno_integer_power
    (h.nonsplit_mass_integer_power_not_mem p hp hp' hnonsplit)

theorem Classical.commensurate_of_nonsplit_mass
    {first second : Rule} (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (hequal : first.criticalDimensions p = second.criticalDimensions q)
    (hno_integer_power : ∀ exponent : ℕ, 0 < exponent →
      ∀ integer : ℤ, deriv first.network.reliability p ^ exponent ≠ integer)
    (hnonsplit : (spectralRadius ℂ ((first.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p}) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) := by
  apply Section4.commensurate_of_three_independent_dimensions hfirst.scale hsecond.scale
    (first.criticalDimensions p)
    (hfirst.criticalDimensions_independent_of_nonsplit_mass p hp hp' hfixedFirst
      hno_integer_power hnonsplit)
  · exact hfirst.exp_log_scale_criticalDimensions_algebraic p hp hp' hfixedFirst
  · rw [hequal]
    exact hsecond.exp_log_scale_criticalDimensions_algebraic q hq hq' hfixedSecond

end
end Universality.Rule

#print axioms Universality.Rule.Classical.criticalDimensions_independent_of_nonsplit_mass
#print axioms Universality.Rule.Classical.commensurate_of_nonsplit_mass
