import Universality.Percolation.RootMomentDominatedConvergence
import Universality.Percolation.AnnealedCriticalMomentFinite

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.root_moment_tendsto_of_geometric_birth_bound {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) < rule.edges)
    (filter : Filter ℝ) (hfilter : Tendsto (fun p : ℝ => p) filter (𝓝 critical))
    (allowed : ℝ → Prop) (hallowed : ∀ p, allowed p → 0 < p ∧ p < 1)
    (heventually : ∀ᶠ p in filter, allowed p)
    (growth : ℝ) (hgrowth : 0 ≤ growth) (hgrowthOne : growth < 1)
    (hdomination : ∃ neighborhood constant : ℝ, 0 < neighborhood ∧ 0 < constant ∧
      ∀ p, allowed p → |p - critical| < neighborhood → ∀ n : ℕ,
        (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1) ≤
          constant * growth ^ n) :
    Tendsto (fun p : ℝ => (rule.limitingRootSizeMoment p order).toReal) filter
      (𝓝 (rule.limitingRootSizeMoment critical order).toReal) := by
  obtain ⟨neighborhood, constant, hneighborhood, hconstant, hb⟩ := hdomination
  have hnear : ∀ᶠ p in 𝓝 critical, |p - critical| < neighborhood := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨neighborhood, hneighborhood, ?_⟩
    intro p hp
    simpa only [Real.dist_eq] using hp
  apply rule.root_moment_tendsto_of_birth_domination h.edges_gt_one h.vertices_gt_two
    critical hc.le hc'.le order filter hfilter
    (heventually.mono (fun p hp => ⟨(hallowed p hp).1.le, (hallowed p hp).2.le⟩))
    (fun n => constant * growth ^ n) ((summable_geometric_of_lt_one hgrowth hgrowthOne).mul_left constant)
  · filter_upwards [heventually, hfilter.eventually hnear] with p hp hnear
    exact hb p hp hnear
  · exact h.critical_root_moment_ne_top critical hc hc' hfixed order hthreshold

end
end Universality.Rule
