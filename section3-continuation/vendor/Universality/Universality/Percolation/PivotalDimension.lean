import Universality.Graph.Iteration
import Universality.Percolation.ConditionalPivotal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto

namespace Universality.Rule
noncomputable section
open FiniteNetwork Filter
open scoped Topology

theorem generation_expected_pivotalCount (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (n : ℕ) :
    expectation p (fun ω => (rule.generation n).network.pivotalCount ω) =
      deriv rule.network.reliability p ^ (n + 1) := by
  rw [← FiniteNetwork.russo_formula]
  exact (rule.generation_hasDerivAt p hfixed n).deriv

theorem generation_conditional_pivotalCount (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hne : p ≠ 0) (n : ℕ) :
    expectation p (fun ω => if (rule.generation n).network.crosses ω then
      ((rule.generation n).network.pivotalCount ω : ℝ) else 0) /
      (rule.generation n).network.reliability p =
        deriv rule.network.reliability p ^ (n + 1) := by
  rw [(rule.generation n).network.conditional_connected_pivotalCount_at_fixed_point p
    (rule.generation_fixed_point p hfixed n) hne]
  exact (rule.generation_hasDerivAt p hfixed n).deriv

def pivotalLogarithmicGrowth (rule : Rule) (p : ℝ) (n : ℕ) : ℝ :=
  Real.log (expectation p (fun ω => (rule.generation n).network.pivotalCount ω)) /
    Real.log ((rule.generation n).network.fullGraph.dist
      (rule.generation n).network.source (rule.generation n).network.target)

theorem pivotalLogarithmicGrowth_eq (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p)
    (reachable : rule.network.fullGraph.Reachable rule.network.source rule.network.target) (n : ℕ) :
    rule.pivotalLogarithmicGrowth p n =
      Real.log (deriv rule.network.reliability p) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) := by
  unfold pivotalLogarithmicGrowth
  rw [generation_expected_pivotalCount rule p hfixed, generation_terminal_distance rule reachable,
    Nat.cast_pow, Real.log_pow, Real.log_pow]
  exact mul_div_mul_left _ _ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)

/-- This proves a limit of genuine finite-graph expected pivotal counts.
The distinguished probability is an interior fixed point supplied by the
caller; identifying it as an infinite-volume threshold is separate. -/
theorem pivotal_dimension (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p)
    (reachable : rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (hderivative : 0 < deriv rule.network.reliability p)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    (∀ n, 0 < expectation p (fun ω => (rule.generation n).network.pivotalCount ω)) ∧
    (∀ n, 0 < Real.log ((rule.generation n).network.fullGraph.dist
      (rule.generation n).network.source (rule.generation n).network.target)) ∧
    Tendsto (rule.pivotalLogarithmicGrowth p) atTop
      (𝓝 (Real.log (deriv rule.network.reliability p) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) := by
  constructor
  · intro n
    rw [generation_expected_pivotalCount rule p hfixed]
    exact pow_pos hderivative _
  constructor
  · intro n
    rw [generation_terminal_distance rule reachable, Nat.cast_pow, Real.log_pow]
    apply mul_pos (by positivity)
    apply Real.log_pos
    exact_mod_cast hscale
  · have hfunction : rule.pivotalLogarithmicGrowth p = fun _ =>
        Real.log (deriv rule.network.reliability p) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) := by
      funext n
      exact rule.pivotalLogarithmicGrowth_eq p hfixed reachable n
    rw [hfunction]
    exact tendsto_const_nhds

end
end Universality.Rule
