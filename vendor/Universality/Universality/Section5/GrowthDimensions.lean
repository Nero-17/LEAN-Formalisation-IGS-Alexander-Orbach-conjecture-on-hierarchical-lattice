import Universality.Section5.CompositionFamily
import Universality.Percolation.ClassicalCriticalPoint

/-! Actual finite-growth limits for rules meeting the Section 5 certificate. -/

namespace Universality.Section5
noncomputable section
open Matrix FiniteNetwork Filter
open scoped Topology

theorem power_log_ratio (base : ℕ) (base_gt_one : 1 < base) (power : ℕ) :
    Real.log ((base : ℝ) ^ power) / Real.log ((base : ℝ) ^ 100) = (power : ℝ) / 100 := by
  rw [Real.log_pow, Real.log_pow]
  have positive : 0 < Real.log (base : ℝ) := Real.log_pos (by exact_mod_cast base_gt_one)
  field_simp
  norm_num

theorem RuleResponses.dimensions {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) (base_gt_one : 1 < base) :
    Real.log (rule.edges : ℝ) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) = 58 / 25 ∧
    Real.log ((_root_.spectralRadius ℂ ((rule.network.massMatrix (1 / 2)).map Complex.ofReal)).toReal) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) = 219 / 100 ∧
    Real.log (deriv rule.network.reliability (1 / 2)) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) = 7 / 10 := by
  simp only [responses.edges, responses.distance, responses.thermal, responses.spectralRadius,
    ENNReal.toReal_ofReal (show 0 ≤ (base : ℝ) ^ 219 by positivity)]
  simp only [Nat.cast_pow]
  rw [power_log_ratio base base_gt_one 232, power_log_ratio base base_gt_one 219,
    power_log_ratio base base_gt_one 70]
  norm_num

/-- All three limits refer to the genuine graphs and conditional masses. -/
theorem RuleResponses.actual_growth_limits {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) (base_gt_one : 1 < base) :
    (∀ n : ℕ, Real.log ((rule.generation n).edges : ℝ) /
      Real.log ((rule.generation n).network.fullGraph.dist
        (rule.generation n).network.source (rule.generation n).network.target) = 58 / 25) ∧
    (∀ state : LiveState, Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalClusterMass (1 / 2) state) /
        Real.log ((rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source (rule.generation n).network.target))
      atTop (𝓝 (219 / 100))) ∧
    Tendsto (rule.pivotalLogarithmicGrowth (1 / 2)) atTop (𝓝 (7 / 10)) := by
  have formulas := rule.finite_three_growth_formulas (1 / 2) (by norm_num) (by norm_num)
    responses.fixed responses.classical.massAdmissible.symmetric responses.classical.scale
  obtain ⟨ambient, mass, pivotal⟩ := responses.dimensions base_gt_one
  simpa only [ambient, mass, pivotal] using formulas

theorem RuleResponses.crossing_transition {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) :
    (∀ p : ℝ, 0 ≤ p → p < 1 / 2 →
      Tendsto (fun n : ℕ => (rule.generation n).network.reliability p) atTop (𝓝 0)) ∧
    (∀ p : ℝ, 1 / 2 < p → p ≤ 1 →
      Tendsto (fun n : ℕ => (rule.generation n).network.reliability p) atTop (𝓝 1)) ∧
    (∀ p : ℝ, 0 < p → p < 1 → rule.network.reliability p = p → p = 1 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p nonnegative below
    exact rule.generation_crossing_tendsto_zero (1 / 2) p (by norm_num) (by norm_num)
      responses.fixed nonnegative below responses.classical.scale
  · intro p above atMostOne
    exact rule.generation_crossing_tendsto_one (1 / 2) p (by norm_num) (by norm_num)
      responses.fixed above atMostOne responses.classical.scale
  · intro p positive belowOne fixed
    exact rule.network.interior_fixed_point_unique p (1 / 2) positive belowOne
      (by norm_num) (by norm_num) fixed responses.fixed responses.classical.scale

theorem compositionFamily_injective {first repeated : Rule}
    (firstResponses : RuleResponses first 19)
    (repeatedResponses : RuleResponses repeated 661) :
    Function.Injective (compositionFamily first repeated) := by
  intro i j equality
  by_contra different
  apply compositionFamily_incommensurate firstResponses repeatedResponses different
  rw [equality]
  exact ScaleCommensurate.refl _

theorem compositionFamily_infinite {first repeated : Rule}
    (firstResponses : RuleResponses first 19)
    (repeatedResponses : RuleResponses repeated 661) :
    Set.Infinite (Set.range (compositionFamily first repeated)) :=
  Set.infinite_range_of_injective (compositionFamily_injective firstResponses repeatedResponses)

/-- These are evaluations of the formulas, not physical exponent existence. -/
theorem four_exponent_values :
    ((58 / 25 : ℝ) - 219 / 100) / (7 / 10) = 13 / 70 ∧
    (1 : ℝ) / (7 / 10) = 10 / 7 ∧
    (219 / 100 : ℝ) / (58 / 25 - 219 / 100) = 219 / 13 ∧
    (2 : ℝ) + 58 / 25 - 2 * (219 / 100) = -3 / 50 := by
  norm_num

end
end Universality.Section5
