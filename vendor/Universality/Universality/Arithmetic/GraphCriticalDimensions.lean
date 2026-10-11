import Universality.Arithmetic.GraphAlgebraicity
import Universality.Arithmetic.ScaleBlocking

/-!
# The three critical finite-growth dimensions of an actual classical rule

These are the closed forms proved by the finite graph growth theory.  The
theorem `criticalDimensions_finite_growth` below identifies them with those
actual growth limits; no infinite-volume identification is assumed.
-/

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

def criticalDimensions (rule : Rule) (p : ℝ) : Fin 3 → ℝ :=
  ![Real.log (rule.edges : ℝ) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target),
    Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target),
    Real.log (deriv rule.network.reliability p) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)]

theorem Classical.edges_pos {rule : Rule} (h : rule.Classical) : 0 < rule.edges := by
  obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (h.connected _)
  exact Nat.zero_lt_of_lt edge.isLt

theorem Classical.criticalDimensions_finite_growth {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) :
    (∀ n : ℕ, Real.log ((rule.generation n).edges : ℝ) /
      Real.log ((rule.generation n).network.fullGraph.dist
        (rule.generation n).network.source (rule.generation n).network.target) =
      rule.criticalDimensions p 0) ∧
    (∀ state : LiveState, Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalClusterMass p state) /
        Real.log ((rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source (rule.generation n).network.target))
      atTop (𝓝 (rule.criticalDimensions p 1))) ∧
    Tendsto (rule.pivotalLogarithmicGrowth p) atTop
      (𝓝 (rule.criticalDimensions p 2)) := by
  exact rule.finite_three_growth_formulas p hp hp' hfixed h.massAdmissible.symmetric h.scale

theorem Classical.exp_log_scale_criticalDimensions_algebraic {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (index : Fin 3) :
    IsAlgebraic ℚ (Real.exp
      (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) *
        rule.criticalDimensions p index)) := by
  have hlog : Real.log
      (rule.network.fullGraph.dist rule.network.source rule.network.target) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast h.scale))
  have hcancel (multiplier : ℝ) (hpositive : 0 < multiplier) :
      Real.exp (Real.log
        (rule.network.fullGraph.dist rule.network.source rule.network.target) *
          (Real.log multiplier / Real.log
            (rule.network.fullGraph.dist rule.network.source rule.network.target))) =
        multiplier := by
    rw [mul_div_cancel₀ _ hlog, Real.exp_log hpositive]
  fin_cases index
  · change IsAlgebraic ℚ (Real.exp (_ * (Real.log (rule.edges : ℝ) / _)))
    rw [hcancel _ (by exact_mod_cast h.edges_pos)]
    exact isAlgebraic_nat rule.edges
  · change IsAlgebraic ℚ (Real.exp (_ * (Real.log
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / _)))
    rw [hcancel _ (h.mass_spectralRadius_positive_eigenvector p hp hp').1]
    exact h.mass_spectralRadius_isAlgebraic p hp hp' hfixed
  · change IsAlgebraic ℚ (Real.exp (_ * (Real.log (deriv rule.network.reliability p) / _)))
    rw [hcancel _ (rule.network.reliability_derivative_pos hp hp' (h.connected _))]
    exact (h.critical_responses_algebraic p hfixed).2.1

end
end Universality.Rule

#print axioms Universality.Rule.Classical.criticalDimensions_finite_growth
#print axioms Universality.Rule.Classical.exp_log_scale_criticalDimensions_algebraic
