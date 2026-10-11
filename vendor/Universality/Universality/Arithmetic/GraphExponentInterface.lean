import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Algebra.ExponentRecovery
import Universality.Percolation.MassSpectralUpperBound

/-!
# Actual graph interface for the finite exponent-formula reconstruction

A triple is supplied externally, in the order `(nu, beta, delta)`. The
`CoreExponentFormula` proposition records three formula equalities as explicit
evidence. It neither defines physical critical exponents nor proves existence
or the formula theorem for an observable. Those are separate obligations.

All denominator conditions below are derived from the actual classical graph:
strict instability gives a positive pivotal dimension, and the strict mass
spectral-radius bound gives a positive ambient-minus-mass gap.
-/

namespace Universality.Rule

noncomputable section
open FiniteNetwork Matrix

/-- Formula evidence for an externally given triple, ordered `nu, beta, delta`.
This proposition does not assert a physical interpretation of that triple. -/
structure CoreExponentFormula (rule : Rule) (p : ℝ) (exponents : Fin 3 → ℝ) : Prop where
  nu_eq : exponents 0 = 1 / rule.criticalDimensions p 2
  beta_eq : exponents 1 =
    (rule.criticalDimensions p 0 - rule.criticalDimensions p 1) / rule.criticalDimensions p 2
  delta_eq : exponents 2 =
    rule.criticalDimensions p 1 / (rule.criticalDimensions p 0 - rule.criticalDimensions p 1)

theorem Classical.criticalDimensions_pivotal_pos {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    0 < rule.criticalDimensions p 2 := by
  exact div_pos
    (Real.log_pos (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale))
    (Real.log_pos (by exact_mod_cast h.scale))

theorem Classical.criticalDimensions_ambient_sub_mass_pos {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    0 < rule.criticalDimensions p 0 - rule.criticalDimensions p 1 := by
  have hmassPositive := (h.mass_spectralRadius_positive_eigenvector p hp hp').1
  have hmassSmaller := h.mass_spectralRadius_lt_edges p hp hp'
  have hscalePositive : 0 < Real.log
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) :=
    Real.log_pos (by exact_mod_cast h.scale)
  exact sub_pos.mpr ((div_lt_div_iff_of_pos_right hscalePositive).mpr
    (Real.log_lt_log hmassPositive hmassSmaller))

/-- Recover all actual finite-growth dimensions from externally supplied
formula evidence. No nonzero denominator premise is supplied by the caller. -/
theorem CoreExponentFormula.recover_dimensions {rule : Rule} {p : ℝ}
    {exponents : Fin 3 → ℝ} (hformula : rule.CoreExponentFormula p exponents)
    (h : rule.Classical) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) :
    rule.criticalDimensions p =
      ![exponents 1 * (exponents 2 + 1) / exponents 0,
        exponents 1 * exponents 2 / exponents 0, 1 / exponents 0] := by
  have hgap := ne_of_gt (h.criticalDimensions_ambient_sub_mass_pos p hp hp')
  have hpivotal := ne_of_gt (h.criticalDimensions_pivotal_pos p hp hp' hfixed)
  funext index
  fin_cases index
  · change rule.criticalDimensions p 0 = _
    rw [hformula.beta_eq, hformula.delta_eq, hformula.nu_eq]
    exact (recover_ambient_from_exponent_formulas _ _ _ hgap hpivotal).symm
  · change rule.criticalDimensions p 1 = _
    rw [hformula.beta_eq, hformula.delta_eq, hformula.nu_eq]
    exact (recover_mass_from_exponent_formulas _ _ _ hgap hpivotal).symm
  · change rule.criticalDimensions p 2 = _
    rw [hformula.nu_eq]
    exact (recover_pivotal_from_exponent_formula _).symm

/-- The finite algebraic reconstruction interface. A physical-class theorem
may use this only after proving both supplied formula-evidence propositions. -/
theorem Classical.coreExponentFormula_eq_iff_criticalDimensions_eq {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstExponents secondExponents : Fin 3 → ℝ)
    (hfirstFormula : first.CoreExponentFormula p firstExponents)
    (hsecondFormula : second.CoreExponentFormula q secondExponents) :
    firstExponents = secondExponents ↔ first.criticalDimensions p = second.criticalDimensions q := by
  constructor
  · intro hequal
    have hbeta : (first.criticalDimensions p 0 - first.criticalDimensions p 1) /
        first.criticalDimensions p 2 =
        (second.criticalDimensions q 0 - second.criticalDimensions q 1) /
        second.criticalDimensions q 2 := by
      rw [← hfirstFormula.beta_eq, ← hsecondFormula.beta_eq, hequal]
    have hnu : 1 / first.criticalDimensions p 2 = 1 / second.criticalDimensions q 2 := by
      rw [← hfirstFormula.nu_eq, ← hsecondFormula.nu_eq, hequal]
    have hdelta : first.criticalDimensions p 1 /
        (first.criticalDimensions p 0 - first.criticalDimensions p 1) =
        second.criticalDimensions q 1 /
        (second.criticalDimensions q 0 - second.criticalDimensions q 1) := by
      rw [← hfirstFormula.delta_eq, ← hsecondFormula.delta_eq, hequal]
    obtain ⟨hambient, hmass, hpivotal⟩ := three_exponent_formulas_injective _ _ _ _ _ _
      (ne_of_gt (hfirst.criticalDimensions_ambient_sub_mass_pos p hp hp'))
      (ne_of_gt (hsecond.criticalDimensions_ambient_sub_mass_pos q hq hq'))
      (ne_of_gt (hfirst.criticalDimensions_pivotal_pos p hp hp' hfixedFirst))
      (ne_of_gt (hsecond.criticalDimensions_pivotal_pos q hq hq' hfixedSecond))
      hbeta hnu hdelta
    funext index
    fin_cases index
    · exact hambient
    · exact hmass
    · exact hpivotal
  · intro hequal
    funext index
    fin_cases index
    · change firstExponents 0 = secondExponents 0
      rw [hfirstFormula.nu_eq, hsecondFormula.nu_eq, hequal]
    · change firstExponents 1 = secondExponents 1
      rw [hfirstFormula.beta_eq, hsecondFormula.beta_eq, hequal]
    · change firstExponents 2 = secondExponents 2
      rw [hfirstFormula.delta_eq, hsecondFormula.delta_eq, hequal]

/-- The eta formula is recovered from the three supplied formula values; this
is an algebraic identity, not an existence theorem for averaged connectivity. -/
theorem CoreExponentFormula.recover_eta_formula {rule : Rule} {p : ℝ}
    {exponents : Fin 3 → ℝ} (hformula : rule.CoreExponentFormula p exponents)
    (h : rule.Classical) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) :
    2 + rule.criticalDimensions p 0 - 2 * rule.criticalDimensions p 1 =
      2 + exponents 1 * (1 - exponents 2) / exponents 0 := by
  rw [hformula.recover_dimensions h hp hp' hfixed]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end
end Universality.Rule

#print axioms Universality.Rule.Classical.criticalDimensions_pivotal_pos
#print axioms Universality.Rule.Classical.criticalDimensions_ambient_sub_mass_pos
#print axioms Universality.Rule.CoreExponentFormula.recover_dimensions
#print axioms Universality.Rule.Classical.coreExponentFormula_eq_iff_criticalDimensions_eq
#print axioms Universality.Rule.CoreExponentFormula.recover_eta_formula

