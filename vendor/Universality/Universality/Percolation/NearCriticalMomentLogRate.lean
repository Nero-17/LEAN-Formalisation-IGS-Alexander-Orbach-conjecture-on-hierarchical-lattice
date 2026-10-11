import Universality.Percolation.CappedNearCriticalRootMoment
import Universality.Percolation.MomentExitTendsto
import Universality.Analysis.StoppedMomentLogRate
import Universality.Percolation.ActualReliabilityExitLogBound
import Universality.Analysis.PowerResponseExponent

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
attribute [local irreducible] limitingRootSizeMoment

theorem Classical.root_moment_log_rate_from_capped_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
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
    (∀ᶠ p in filter, 0 < (rule.limitingRootSizeMoment p order).toReal) ∧
    Tendsto (fun p : ℝ => Real.log (rule.limitingRootSizeMoment p order).toReal / Real.log |p - critical|)
      filter (𝓝 (-max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)) 0 /
          Real.log (deriv rule.network.reliability critical))) := by
  obtain ⟨cap, hcap, _, _, hescape⟩ := h.reliability_exit_log_bound critical hc hc' hfixed
  obtain ⟨radius, neighborhood, lower, upper, hradius, hradiusCritical, hradiusOne, hradiusCap,
    hneighborhood, hlower, hupper, hb⟩ := hcomparison cap hcap
  obtain ⟨bound, hbound, htime⟩ := hescape radius hradius hradiusCap
  have hinterior : ∀ᶠ p in filter, 0 < p ∧ p < 1 ∧ p ≠ critical :=
    heventually.mono (fun p hp => hallowed p hp)
  have hdepth := h.reliability_exit_tendsto_atTop critical radius hc hc' hfixed hradius
    hradiusCritical hradiusOne filter hfilter hinterior
  have hm : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hgrowth : 0 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hnear : ∀ᶠ p in 𝓝 critical, |p - critical| < neighborhood := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨neighborhood, hneighborhood, ?_⟩
    intro p hp
    simpa only [Real.dist_eq] using hp
  have hbounds := (heventually.and (hfilter.eventually hnear)).mono
    (fun p hp => (hb p hp.1 hp.2).2)
  refine ⟨?_, ?_⟩
  · filter_upwards [hbounds, hdepth.eventually (eventually_ge_atTop 1)] with p hp hn
    have hratio : 0 < ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges :=
      div_pos (pow_pos hgrowth _) hm
    have hsum := Finset.single_le_sum
      (s := Finset.range (rule.reliabilityExitTime critical radius p))
      (f := fun n => (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1))
      (fun n _ => (pow_pos hratio _).le)
      (Finset.mem_range.mpr (show 0 < rule.reliabilityExitTime critical radius p by omega))
    have hsumPos : 0 < ∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1) :=
      hratio.trans_le (by simpa only [zero_add, pow_one] using hsum)
    exact (mul_pos hlower hsumPos).trans_le hp.1
  · apply stopped_moment_logarithmic_exponent filter
      (fun p => (rule.limitingRootSizeMoment p order).toReal) (fun p => Real.log |p - critical|)
      (rule.reliabilityExitTime critical radius)
      _ (deriv rule.network.reliability critical) lower upper bound hdepth hdeviation
      (div_pos (pow_pos hgrowth _) hm)
      (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale) hlower hupper
    · exact hbounds
    · filter_upwards [hinterior] with p hp
      exact htime p hp.1 hp.2.1 hp.2.2

end
end Universality.Rule
