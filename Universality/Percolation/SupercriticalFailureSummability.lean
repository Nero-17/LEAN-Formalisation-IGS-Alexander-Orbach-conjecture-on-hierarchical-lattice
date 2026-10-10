import Universality.Analysis.ZeroDerivativeIteration
import Universality.Percolation.RenormalisationLimits
import Universality.Graph.ClassicalRule

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.supercritical_iterate_failure_weighted_summable {rule : Rule} (h : rule.Classical)
    (critical p growth : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hpc : critical < p) (hp' : p ≤ 1)
    (hgrowth : 0 < growth) :
    Summable (fun n : ℕ => growth ^ n * (1 - rule.network.reliability^[n] p)) := by
  have hderivative : HasDerivAt rule.network.reliability 0 1 := by
    have hd := (rule.network.hasDerivAt_reliability 1).differentiableAt.hasDerivAt
    rwa [rule.network.derivative_one_zero h.cut] at hd
  have hs := summable_weighted_iterate_sub_of_derivative_zero
    rule.network.reliability p 1 growth hgrowth (rule.network.reliability_one (h.connected _)) hderivative
    (rule.network.iterate_reliability_tendsto_one critical p hc hc' hfixed hpc hp' h.scale)
  exact hs.neg.congr (fun n => by ring)

/-- The actual finite-cell failure probabilities are summable after any
geometric amplification throughout the supercritical parameter interval. -/
theorem Classical.supercritical_generation_failure_weighted_summable {rule : Rule} (h : rule.Classical)
    (critical p growth : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hpc : critical < p) (hp' : p ≤ 1)
    (hgrowth : 0 < growth) :
    Summable (fun n : ℕ => growth ^ n * (1 - (rule.generation n).network.reliability p)) := by
  have hs := h.supercritical_iterate_failure_weighted_summable critical p growth hc hc' hfixed hpc hp' hgrowth
  have hshift := (hs.comp_injective (fun a b (hab : a + 1 = b + 1) => Nat.add_right_cancel hab)).div_const growth
  exact hshift.congr (fun n => by
    simp only [Function.comp_def]
    rw [rule.generation_reliability_iterate, pow_succ]
    field_simp [hgrowth.ne'])

end
end Universality.Rule
