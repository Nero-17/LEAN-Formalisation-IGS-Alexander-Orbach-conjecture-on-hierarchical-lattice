import Universality.Graph.Section5Classical

namespace Universality.Section5
noncomputable section
open Filter
open scoped Topology

/-- At one half the finite crossing probabilities stay fixed, while every
parameter below or above it converges to the corresponding endpoint. -/
theorem WheatstoneExpression.finite_crossing_transition_half (expression : WheatstoneExpression)
    (nontrivial : expression ≠ .edge) :
    expression.rule.network.reliability (1 / 2) = 1 / 2 ∧
      1 < deriv expression.rule.network.reliability (1 / 2) ∧
      (∀ p : ℝ, 0 ≤ p → p < 1 / 2 →
        Tendsto (fun n : ℕ => (expression.rule.generation n).network.reliability p) atTop (𝓝 0)) ∧
      (∀ p : ℝ, 1 / 2 < p → p ≤ 1 →
        Tendsto (fun n : ℕ => (expression.rule.generation n).network.reliability p) atTop (𝓝 1)) ∧
      (∀ p : ℝ, 0 < p → p < 1 → expression.rule.network.reliability p = p → p = 1 / 2) := by
  have classical := expression.classical nontrivial
  refine ⟨expression.fixed_half,
    expression.rule.network.interior_fixed_point_strictly_unstable (1 / 2)
      (by norm_num) (by norm_num) expression.fixed_half classical.scale, ?_, ?_, ?_⟩
  · intro p positive below
    exact expression.rule.generation_crossing_tendsto_zero (1 / 2) p
      (by norm_num) (by norm_num) expression.fixed_half positive below classical.scale
  · intro p above less_one
    exact expression.rule.generation_crossing_tendsto_one (1 / 2) p
      (by norm_num) (by norm_num) expression.fixed_half above less_one classical.scale
  · exact expression.unique_interior_fixed_point nontrivial

end
end Universality.Section5
