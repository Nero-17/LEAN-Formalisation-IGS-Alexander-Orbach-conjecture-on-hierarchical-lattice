import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Arithmetic.WheatstoneArithmetic
import Universality.Examples.ClassicalSeeds

/-!
# The whole-class Wheatstone scale conclusion for actual graph rules

Only the ambient and pivotal dimensions are used. The other representative's
algebraic-exponential obligations are proved from its graph responses.
-/

namespace Universality
noncomputable section

theorem wheatstone_ambient_criticalDimension :
    wheatstoneRule.criticalDimensions (1 / 2) 0 = Real.log 5 / Real.log 2 := by
  simp [Rule.criticalDimensions, wheatstoneRule, wheatstone_terminal_distance]

theorem wheatstone_pivotal_criticalDimension :
    wheatstoneRule.criticalDimensions (1 / 2) 2 = Real.log (13 / 8) / Real.log 2 := by
  change Real.log (deriv wheatstoneNetwork.reliability (1 / 2)) /
    Real.log (wheatstoneNetwork.fullGraph.dist wheatstoneNetwork.source wheatstoneNetwork.target) = _
  rw [wheatstone_terminal_distance, wheatstone_deriv_half]
  norm_num

theorem wheatstone_actual_criticalDimensions_independent :
    LinearIndependent ℚ ![(1 : ℝ), wheatstoneRule.criticalDimensions (1 / 2) 0,
      wheatstoneRule.criticalDimensions (1 / 2) 2] := by
  rw [wheatstone_ambient_criticalDimension, wheatstone_pivotal_criticalDimension]
  exact Section4.wheatstone_three_dimensions_independent

theorem Rule.Classical.scale_power_two_of_wheatstone_dimensions {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p)
    (hambient : rule.criticalDimensions p 0 = wheatstoneRule.criticalDimensions (1 / 2) 0)
    (hpivotal : rule.criticalDimensions p 2 = wheatstoneRule.criticalDimensions (1 / 2) 2) :
    ∃ exponent : ℕ, 0 < exponent ∧
      rule.network.fullGraph.dist rule.network.source rule.network.target = 2 ^ exponent := by
  apply Section4.wheatstone_scale_is_power_two _ h.scale
  intro index
  fin_cases index
  · change IsAlgebraic ℚ (Real.exp
      (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) * 1))
    rw [mul_one, Real.exp_log (by exact_mod_cast (lt_trans Nat.zero_lt_one h.scale))]
    exact isAlgebraic_nat _
  · have halgebraic := h.exp_log_scale_criticalDimensions_algebraic p hp hp' hfixed 0
    rw [hambient, wheatstone_ambient_criticalDimension] at halgebraic
    exact halgebraic
  · have halgebraic := h.exp_log_scale_criticalDimensions_algebraic p hp hp' hfixed 2
    rw [hpivotal, wheatstone_pivotal_criticalDimension] at halgebraic
    exact halgebraic

end
end Universality

#print axioms Universality.wheatstone_actual_criticalDimensions_independent
#print axioms Universality.Rule.Classical.scale_power_two_of_wheatstone_dimensions
