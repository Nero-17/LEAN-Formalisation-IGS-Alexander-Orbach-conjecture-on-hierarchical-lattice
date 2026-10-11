import Universality.Percolation.SupercriticalFailureSummability

namespace Universality.Rule
noncomputable section

theorem Classical.subcritical_iterate_crossing_weighted_summable {rule : Rule} (h : rule.Classical)
    (critical p growth : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical)
    (hgrowth : 0 < growth) :
    Summable (fun n : ℕ => growth ^ n * rule.network.reliability^[n] p) := by
  have hderivative : HasDerivAt rule.network.reliability 0 0 := by
    have hd := (rule.network.hasDerivAt_reliability 0).differentiableAt.hasDerivAt
    rwa [rule.network.derivative_zero_zero h.scale] at hd
  simpa only [sub_zero] using summable_weighted_iterate_sub_of_derivative_zero
    rule.network.reliability p 0 growth hgrowth rule.network.reliability_zero hderivative
    (rule.network.iterate_reliability_tendsto_zero critical p hc hc' hfixed hp hpc h.scale)

theorem Classical.subcritical_generation_crossing_weighted_summable {rule : Rule} (h : rule.Classical)
    (critical p growth : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical)
    (hgrowth : 0 < growth) :
    Summable (fun n : ℕ => growth ^ n * (rule.generation n).network.reliability p) := by
  have hs := h.subcritical_iterate_crossing_weighted_summable critical p growth hc hc' hfixed hp hpc hgrowth
  have hshift := (hs.comp_injective (fun a b (hab : a + 1 = b + 1) => Nat.add_right_cancel hab)).div_const growth
  exact hshift.congr (fun n => by
    simp only [Function.comp_def]
    rw [rule.generation_reliability_iterate, pow_succ]
    field_simp [hgrowth.ne'])

end
end Universality.Rule
