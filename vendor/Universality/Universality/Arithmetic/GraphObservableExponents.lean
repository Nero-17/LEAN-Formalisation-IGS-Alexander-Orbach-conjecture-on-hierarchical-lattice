import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Percolation.CrossingExponent
import Universality.Percolation.EscapingRootMassExponent

/-!
Actual observable limits expressed in the Section 4 dimension coordinates.

The crossing correlation length is the genuine iterated-reliability limit.
The escaping mass is the missing mass of the limiting finite-volume uniform
root size law. Identification of that mass with the infinite-cluster
probability on the uniformly rooted infinite graph is a separate obligation.
No such identification is asserted or assumed in this module.
-/

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.crossing_length_exponent_criticalDimensions {rule : Rule}
    (h : rule.Classical) (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Tendsto
      (fun p : ℝ => -Real.log (rule.network.crossingCorrelationLength p) /
        Real.log (critical - p))
      (𝓝[<] critical) (𝓝 (1 / rule.criticalDimensions critical 2)) := by
  have hvalue : 1 / rule.criticalDimensions critical 2 =
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
        Real.log (deriv rule.network.reliability critical) := by
    change 1 / (Real.log (deriv rule.network.reliability critical) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)) = _
    simp only [one_div, inv_div]
  rw [hvalue]
  exact h.crossing_length_exponent critical hc hc' hfixed

theorem Classical.escaping_root_mass_exponent_criticalDimensions {rule : Rule}
    (h : rule.Classical) (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Tendsto
      (fun p : ℝ => Real.log (rule.escapingRootMass p) / Real.log (p - critical))
      (𝓝[>] critical)
      (𝓝 ((rule.criticalDimensions critical 0 - rule.criticalDimensions critical 1) /
        rule.criticalDimensions critical 2)) := by
  have hlog : Real.log
      (rule.network.fullGraph.dist rule.network.source rule.network.target) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast h.scale))
  have hvalue :
      (rule.criticalDimensions critical 0 - rule.criticalDimensions critical 1) /
        rule.criticalDimensions critical 2 =
      (Real.log (rule.edges : ℝ) - Real.log
        ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)) /
          Real.log (deriv rule.network.reliability critical) := by
    change ((Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) -
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)) /
      (Real.log (deriv rule.network.reliability critical) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) = _
    rw [← sub_div, div_div_div_cancel_right₀ hlog]
  rw [hvalue]
  exact h.escaping_root_mass_exponent critical hc hc' hfixed

/-- Any actual crossing-length logarithmic limit has this dimension value. -/
theorem Classical.crossing_length_exponent_eq_criticalDimensions {rule : Rule}
    (h : rule.Classical) (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (exponent : ℝ)
    (hlimit : Tendsto
      (fun p : ℝ => -Real.log (rule.network.crossingCorrelationLength p) /
        Real.log (critical - p))
      (𝓝[<] critical) (𝓝 exponent)) :
    exponent = 1 / rule.criticalDimensions critical 2 :=
  tendsto_nhds_unique hlimit
    (h.crossing_length_exponent_criticalDimensions critical hc hc' hfixed)

/-- Any actual escaping-mass logarithmic limit has this dimension value. -/
theorem Classical.escaping_root_mass_exponent_eq_criticalDimensions {rule : Rule}
    (h : rule.Classical) (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (exponent : ℝ)
    (hlimit : Tendsto
      (fun p : ℝ => Real.log (rule.escapingRootMass p) / Real.log (p - critical))
      (𝓝[>] critical) (𝓝 exponent)) :
    exponent = (rule.criticalDimensions critical 0 - rule.criticalDimensions critical 1) /
      rule.criticalDimensions critical 2 :=
  tendsto_nhds_unique hlimit
    (h.escaping_root_mass_exponent_criticalDimensions critical hc hc' hfixed)

end
end Universality.Rule

#print axioms Universality.Rule.Classical.crossing_length_exponent_criticalDimensions
#print axioms Universality.Rule.Classical.escaping_root_mass_exponent_criticalDimensions
#print axioms Universality.Rule.Classical.crossing_length_exponent_eq_criticalDimensions
#print axioms Universality.Rule.Classical.escaping_root_mass_exponent_eq_criticalDimensions
