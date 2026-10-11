import Universality.Percolation.MomentExitCompact

namespace Universality.Rule
noncomputable section

theorem Classical.reliability_wide_compact {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1) :
    0 < rule.network.reliability (critical / 2) ∧
      rule.network.reliability ((1 + critical) / 2) < 1 ∧
      rule.network.reliability (critical / 2) ≤ rule.network.reliability ((1 + critical) / 2) := by
  refine ⟨(rule.network.reliability_pos_iff_connected (by linarith) (by linarith)).mpr (h.connected _),
    rule.network.reliability_lt_one (by linarith) (by linarith), ?_⟩
  exact rule.network.reliability_monotoneOn ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ (by linarith)

theorem Classical.reliability_exit_wide_compact {rule : Rule} (h : rule.Classical)
    (critical radius p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hradius : 0 < radius)
    (hradiusCritical : radius ≤ critical / 2) (hradiusOne : radius ≤ (1 - critical) / 2)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) (hnear : |p - critical| < radius) :
    rule.network.reliability^[rule.reliabilityExitTime critical radius p] p ∈
      Set.Icc (rule.network.reliability (critical / 2)) (rule.network.reliability ((1 + critical) / 2)) := by
  have hsmall : radius < critical := by linarith
  have hsmall' : radius < 1 - critical := by linarith
  have hb := (h.reliability_exit_compact critical radius hc hc' hfixed hradius hsmall hsmall').2.2.2.2
    p hp hp' hne hnear
  have hleft : rule.network.reliability (critical / 2) ≤ rule.network.reliability (critical - radius) :=
    rule.network.reliability_monotoneOn ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  have hright : rule.network.reliability (critical + radius) ≤ rule.network.reliability ((1 + critical) / 2) :=
    rule.network.reliability_monotoneOn ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  exact ⟨hleft.trans hb.1.1, hb.1.2.trans hright⟩

end
end Universality.Rule
