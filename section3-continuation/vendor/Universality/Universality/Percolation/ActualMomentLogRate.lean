import Universality.Percolation.NearCriticalMomentLogRate

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
attribute [local irreducible] limitingRootSizeMoment

theorem Classical.supercritical_root_moment_log_rate {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) :
    (∀ᶠ p in 𝓝[>] critical, 0 < (rule.limitingRootSizeMoment p order).toReal) ∧
    Tendsto (fun p : ℝ => Real.log (rule.limitingRootSizeMoment p order).toReal / Real.log |p - critical|)
      (𝓝[>] critical) (𝓝 (-max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)) 0 /
          Real.log (deriv rule.network.reliability critical))) := by
  apply h.root_moment_log_rate_from_capped_comparison critical hc hc' hfixed order
    (𝓝[>] critical) (tendsto_id'.mpr nhdsWithin_le_nhds) (tendsto_log_abs_deviation_right critical)
    (fun p => critical < p ∧ p < 1)
  · intro p hp
    exact ⟨hc.trans hp.1, hp.2, ne_of_gt hp.1⟩
  · have hupper : ∀ᶠ p in 𝓝 critical, p < 1 := Iio_mem_nhds hc'
    filter_upwards [self_mem_nhdsWithin, hupper.filter_mono nhdsWithin_le_nhds] with p hp hu
    exact ⟨hp, hu⟩
  · intro cap hcap
    exact h.supercritical_capped_nearcritical_root_moment_comparison critical hc hc' hfixed order cap hcap

theorem Classical.subcritical_root_moment_log_rate {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) < rule.edges) :
    (∀ᶠ p in 𝓝[<] critical, 0 < (rule.limitingRootSizeMoment p order).toReal) ∧
    Tendsto (fun p : ℝ => Real.log (rule.limitingRootSizeMoment p order).toReal / Real.log |p - critical|)
      (𝓝[<] critical) (𝓝 (-max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)) 0 /
          Real.log (deriv rule.network.reliability critical))) := by
  apply h.root_moment_log_rate_from_capped_comparison critical hc hc' hfixed order
    (𝓝[<] critical) (tendsto_id'.mpr nhdsWithin_le_nhds) (tendsto_log_abs_deviation_left critical)
    (fun p => 0 < p ∧ p < critical)
  · intro p hp
    exact ⟨hp.1, hp.2.trans hc', ne_of_lt hp.2⟩
  · have hlower : ∀ᶠ p in 𝓝 critical, 0 < p := Ioi_mem_nhds hc
    filter_upwards [self_mem_nhdsWithin, hlower.filter_mono nhdsWithin_le_nhds] with p hp hl
    exact ⟨hl, hp⟩
  · intro cap hcap
    exact h.subcritical_capped_nearcritical_root_moment_comparison critical hc hc' hfixed order cap hcap hthreshold

end
end Universality.Rule
