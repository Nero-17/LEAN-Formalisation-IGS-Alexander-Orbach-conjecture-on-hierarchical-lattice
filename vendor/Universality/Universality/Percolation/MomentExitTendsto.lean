import Universality.Percolation.MomentExitTime

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.reliability_exit_tendsto_atTop {rule : Rule} (h : rule.Classical)
    (critical radius : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hradius : 0 < radius)
    (hradiusCritical : radius < critical) (hradiusOne : radius < 1 - critical)
    (filter : Filter ℝ) (hfilter : Tendsto (fun p : ℝ => p) filter (𝓝 critical))
    (hinterior : ∀ᶠ p in filter, 0 < p ∧ p < 1 ∧ p ≠ critical) :
    Tendsto (rule.reliabilityExitTime critical radius) filter atTop := by
  apply tendsto_atTop.2
  intro depth
  obtain ⟨neighborhood, hneighborhood, hb⟩ := h.reliability_exit_diverges critical radius
    hc hc' hfixed hradius hradiusCritical hradiusOne depth
  have hnear : ∀ᶠ p in 𝓝 critical, |p - critical| < neighborhood := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨neighborhood, hneighborhood, ?_⟩
    intro p hp
    simpa only [Real.dist_eq] using hp
  filter_upwards [hinterior, hfilter.eventually hnear] with p hp hnear
  exact (hb p hp.1 hp.2.1 hp.2.2 hnear).le

end
end Universality.Rule
