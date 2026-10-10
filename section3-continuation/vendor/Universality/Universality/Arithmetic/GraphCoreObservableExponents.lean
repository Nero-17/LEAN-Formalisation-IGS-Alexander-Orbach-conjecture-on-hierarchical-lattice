import Universality.Arithmetic.GraphObservableExponents
import Universality.Arithmetic.GraphObservableDelta
import Universality.Arithmetic.GraphExponentInterface

/-!
The three core exponents are specified by actual observable limits. Their
formulas are conclusions of proved finite-volume thermodynamic theorems, not
fields in this structure. The escaping mass and size law have not here been
identified with percolation on a uniformly rooted infinite graph.
-/

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- Actual crossing, escaping-mass and critical size logarithmic limits,
ordered as nu, beta, delta. -/
structure CoreObservableExponents (rule : Rule) (critical : ℝ) (exponents : Fin 3 → ℝ) : Prop where
  nu_limit : Tendsto
    (fun p : ℝ => -Real.log (rule.network.crossingCorrelationLength p) / Real.log (critical - p))
    (𝓝[<] critical) (𝓝 (exponents 0))
  beta_limit : Tendsto
    (fun p : ℝ => Real.log (rule.escapingRootMass p) / Real.log (p - critical))
    (𝓝[>] critical) (𝓝 (exponents 1))
  inverse_delta_limit : Tendsto
    (fun size : ℕ => -1 - Real.log (rule.limitingRootSizeProbability critical size) / Real.log (size : ℝ))
    atTop (𝓝 (1 / exponents 2))

/-- The actual observable limits imply the core exponent formulas. -/
theorem CoreObservableExponents.to_formula {rule : Rule} {critical : ℝ} {exponents : Fin 3 → ℝ}
    (limits : rule.CoreObservableExponents critical exponents) (h : rule.Classical)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : rule.network.reliability critical = critical) :
    rule.CoreExponentFormula critical exponents where
  nu_eq := h.crossing_length_exponent_eq_criticalDimensions critical hc hc' hfixed
    (exponents 0) limits.nu_limit
  beta_eq := h.escaping_root_mass_exponent_eq_criticalDimensions critical hc hc' hfixed
    (exponents 1) limits.beta_limit
  delta_eq := h.critical_delta_eq_criticalDimensions critical hc hc' hfixed
    (exponents 2) limits.inverse_delta_limit

/-- Equality of these actual thermodynamic exponents is equivalent to equality
of the graph's three growth coordinates. -/
theorem Classical.coreObservableExponents_eq_iff_criticalDimensions_eq {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstExponents secondExponents : Fin 3 → ℝ)
    (hfirstLimits : first.CoreObservableExponents p firstExponents)
    (hsecondLimits : second.CoreObservableExponents q secondExponents) :
    firstExponents = secondExponents ↔ first.criticalDimensions p = second.criticalDimensions q :=
  hfirst.coreExponentFormula_eq_iff_criticalDimensions_eq hsecond p q hp hp' hq hq'
    hfixedFirst hfixedSecond firstExponents secondExponents
    (hfirstLimits.to_formula hfirst hp hp' hfixedFirst)
    (hsecondLimits.to_formula hsecond hq hq' hfixedSecond)

/-- The three thermodynamic exponents exist and are uniquely determined by
the actual observable limits. -/
theorem Classical.existsUnique_coreObservableExponents {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃! exponents : Fin 3 → ℝ, rule.CoreObservableExponents critical exponents := by
  refine ⟨![1 / rule.criticalDimensions critical 2,
    (rule.criticalDimensions critical 0 - rule.criticalDimensions critical 1) /
      rule.criticalDimensions critical 2,
    rule.criticalDimensions critical 1 /
      (rule.criticalDimensions critical 0 - rule.criticalDimensions critical 1)], ?_, ?_⟩
  · exact ⟨h.crossing_length_exponent_criticalDimensions critical hc hc' hfixed,
      h.escaping_root_mass_exponent_criticalDimensions critical hc hc' hfixed,
      h.critical_inverse_delta_criticalDimensions critical hc hc' hfixed⟩
  · intro exponents hlimits
    have hformula := hlimits.to_formula h hc hc' hfixed
    funext index
    fin_cases index
    · exact hformula.nu_eq
    · exact hformula.beta_eq
    · exact hformula.delta_eq

/-- Each exponent specified by these actual logarithmic limits is positive. -/
theorem CoreObservableExponents.positive {rule : Rule} {critical : ℝ} {exponents : Fin 3 → ℝ}
    (limits : rule.CoreObservableExponents critical exponents) (h : rule.Classical)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : rule.network.reliability critical = critical)
    (index : Fin 3) : 0 < exponents index := by
  have hformula := limits.to_formula h hc hc' hfixed
  fin_cases index
  · change 0 < exponents 0
    rw [hformula.nu_eq]
    exact one_div_pos.mpr (h.criticalDimensions_pivotal_pos critical hc hc' hfixed)
  · change 0 < exponents 1
    rw [hformula.beta_eq]
    exact div_pos (h.criticalDimensions_ambient_sub_mass_pos critical hc hc')
      (h.criticalDimensions_pivotal_pos critical hc hc' hfixed)
  · change 0 < exponents 2
    rw [hformula.delta_eq]
    exact h.critical_delta_criticalDimensions_pos critical hc hc' hfixed
end
end Universality.Rule

#print axioms Universality.Rule.CoreObservableExponents.to_formula
#print axioms Universality.Rule.Classical.coreObservableExponents_eq_iff_criticalDimensions_eq
#print axioms Universality.Rule.Classical.existsUnique_coreObservableExponents
#print axioms Universality.Rule.CoreObservableExponents.positive
