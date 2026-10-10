import Universality.Percolation.BernoulliMonotonicity
import Universality.Percolation.SupercriticalFailureSummability

namespace Universality.Rule
noncomputable section

/-- Arbitrarily strong geometric bounds hold uniformly throughout a
supercritical interval separated from the critical parameter. -/
theorem Classical.supercritical_uniform_failure_bound {rule : Rule} (h : rule.Classical)
    (critical lower growth : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hlower : critical < lower) (hlower' : lower ≤ 1) (hgrowth : 0 < growth) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ p, lower ≤ p → p ≤ 1 → ∀ n,
      growth ^ n * (1 - (rule.generation n).network.reliability p) ≤ constant := by
  have hs := h.supercritical_generation_failure_weighted_summable critical lower growth
    hc hc' hfixed hlower hlower' hgrowth
  have hnonneg (n : ℕ) : 0 ≤ growth ^ n * (1 - (rule.generation n).network.reliability lower) :=
    mul_nonneg (pow_nonneg hgrowth.le _) (sub_nonneg.mpr
      ((rule.generation n).network.reliability_le_one (hc.trans hlower).le hlower'))
  refine ⟨1 + ∑' n : ℕ, growth ^ n * (1 - (rule.generation n).network.reliability lower),
    add_pos_of_pos_of_nonneg zero_lt_one (tsum_nonneg hnonneg), ?_⟩
  intro p hp hp' n
  have hmono := (rule.generation n).network.reliability_monotoneOn
    ⟨(hc.trans hlower).le, hlower'⟩ ⟨((hc.trans hlower).trans_le hp).le, hp'⟩ hp
  have hterm := hs.sum_le_tsum {n} (fun j _ => hnonneg j)
  simp only [Finset.sum_singleton] at hterm
  have hh := mul_le_mul_of_nonneg_left (show 1 - (rule.generation n).network.reliability p ≤
    1 - (rule.generation n).network.reliability lower by linarith) (pow_nonneg hgrowth.le n)
  linarith

end
end Universality.Rule
