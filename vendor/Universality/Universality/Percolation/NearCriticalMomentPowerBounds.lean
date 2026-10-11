import Universality.Percolation.CappedNearCriticalRootMoment
import Universality.Percolation.MomentExitTendsto
import Universality.Analysis.StoppedGeometricPowerBounds
import Universality.Percolation.ActualReliabilityExitLogBound

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 0
attribute [local irreducible] limitingRootSizeMoment

theorem Classical.root_moment_power_bounds_from_capped_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hpower : (rule.edges : ℝ) < ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1))
    (filter : Filter ℝ) (hfilter : Tendsto (fun p : ℝ => p) filter (𝓝 critical))
    (allowed : ℝ → Prop) (hallowed : ∀ p, allowed p → 0 < p ∧ p < 1 ∧ p ≠ critical)
    (heventually : ∀ᶠ p in filter, allowed p)
    (hcomparison : ∀ cap : ℝ, 0 < cap →
      ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧ radius ≤ cap ∧
      0 < neighborhood ∧ 0 < lower ∧ 0 < upper ∧ ∀ p, allowed p → |p - critical| < neighborhood →
        rule.limitingRootSizeMoment p order ≠ ⊤ ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) ≤
          (rule.limitingRootSizeMoment p order).toReal ∧
        (rule.limitingRootSizeMoment p order).toReal ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1))) :
    ∃ first last : ℝ, 0 < first ∧ 0 < last ∧ ∀ᶠ p in filter,
      first * |p - critical| ^ (-Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) / Real.log (deriv rule.network.reliability critical)) ≤ (rule.limitingRootSizeMoment p order).toReal ∧
      (rule.limitingRootSizeMoment p order).toReal ≤ last * |p - critical| ^ (-Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) / Real.log (deriv rule.network.reliability critical)) := by
  obtain ⟨cap, hcap, _, _, hescape⟩ := h.reliability_exit_log_bound critical hc hc' hfixed
  obtain ⟨radius, neighborhood, lower, upper, hradius, hradiusCritical, hradiusOne, hradiusCap,
    hneighborhood, hlower, hupper, hb⟩ := hcomparison cap hcap
  obtain ⟨bound, _, htime⟩ := hescape radius hradius hradiusCap
  have hinterior : ∀ᶠ p in filter, 0 < p ∧ p < 1 ∧ p ≠ critical :=
    heventually.mono (fun p hp => hallowed p hp)
  have hdepth := h.reliability_exit_tendsto_atTop critical radius hc hc' hfixed hradius
    hradiusCritical hradiusOne filter hfilter hinterior
  have hm : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hnear : ∀ᶠ p in 𝓝 critical, |p - critical| < neighborhood := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨neighborhood, hneighborhood, ?_⟩
    intro p hp
    simpa only [Real.dist_eq] using hp
  have hbounds := (heventually.and (hfilter.eventually hnear)).mono
    (fun p hp => (hb p hp.1 hp.2).2)
  have hratioAbove : 1 < (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) := (one_lt_div hm).mpr hpower
  obtain ⟨first, last, hfirst, hlast, hpowerBounds⟩ := stopped_geometric_power_comparison
    (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) (deriv rule.network.reliability critical) lower upper bound hratioAbove
    (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale) hlower hupper
  refine ⟨first, last, hfirst, hlast, ?_⟩
  filter_upwards [hbounds, hinterior, hdepth.eventually (eventually_ge_atTop 1)] with p hp hi hn
  exact hpowerBounds _ hn |p - critical| (rule.limitingRootSizeMoment p order).toReal
    (abs_pos.mpr (sub_ne_zero.mpr hi.2.2)) hp.1 hp.2 (htime p hi.1 hi.2.1 hi.2.2)

theorem Classical.root_moment_log_bounds_from_capped_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hpower : ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) = (rule.edges : ℝ))
    (filter : Filter ℝ) (hfilter : Tendsto (fun p : ℝ => p) filter (𝓝 critical))
    (hdeviation : Tendsto (fun p : ℝ => Real.log |p - critical|) filter atBot)
    (allowed : ℝ → Prop) (hallowed : ∀ p, allowed p → 0 < p ∧ p < 1 ∧ p ≠ critical)
    (heventually : ∀ᶠ p in filter, allowed p)
    (hcomparison : ∀ cap : ℝ, 0 < cap →
      ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧ radius ≤ cap ∧
      0 < neighborhood ∧ 0 < lower ∧ 0 < upper ∧ ∀ p, allowed p → |p - critical| < neighborhood →
        rule.limitingRootSizeMoment p order ≠ ⊤ ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) ≤
          (rule.limitingRootSizeMoment p order).toReal ∧
        (rule.limitingRootSizeMoment p order).toReal ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1))) :
    ∃ first last : ℝ, 0 < first ∧ 0 < last ∧ ∀ᶠ p in filter,
      first * (-Real.log |p - critical|) ≤ (rule.limitingRootSizeMoment p order).toReal ∧
      (rule.limitingRootSizeMoment p order).toReal ≤ last * (-Real.log |p - critical|) := by
  obtain ⟨cap, hcap, _, _, hescape⟩ := h.reliability_exit_log_bound critical hc hc' hfixed
  obtain ⟨radius, neighborhood, lower, upper, hradius, hradiusCritical, hradiusOne, hradiusCap,
    hneighborhood, hlower, hupper, hb⟩ := hcomparison cap hcap
  obtain ⟨bound, _, htime⟩ := hescape radius hradius hradiusCap
  have hinterior : ∀ᶠ p in filter, 0 < p ∧ p < 1 ∧ p ≠ critical :=
    heventually.mono (fun p hp => hallowed p hp)
  have hm : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hnear : ∀ᶠ p in 𝓝 critical, |p - critical| < neighborhood := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨neighborhood, hneighborhood, ?_⟩
    intro p hp
    simpa only [Real.dist_eq] using hp
  have hbounds := (heventually.and (hfilter.eventually hnear)).mono
    (fun p hp => (hb p hp.1 hp.2).2)
  have hratioOne : (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) = 1 := by rw [hpower, div_self hm.ne']
  obtain ⟨first, last, hfirst, hlast, hlinear⟩ := stopped_linear_log_comparison
    (deriv rule.network.reliability critical) lower upper
    (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale) hlower hupper
  refine ⟨first, last, hfirst, hlast, ?_⟩
  filter_upwards [hbounds, hinterior, hdeviation.eventually (eventually_le_atBot (-2 * bound))] with p hp hi hsmall
  apply hlinear (rule.reliabilityExitTime critical radius p) (Real.log |p - critical|)
    (rule.limitingRootSizeMoment p order).toReal bound
  · simpa only [hratioOne, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using hp.1
  · simpa only [hratioOne, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using hp.2
  · exact htime p hi.1 hi.2.1 hi.2.2
  · exact hsmall

end
end Universality.Rule
