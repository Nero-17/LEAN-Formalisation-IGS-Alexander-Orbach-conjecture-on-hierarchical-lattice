import Universality.Percolation.EscapingRootMassExitBounds
import Universality.Analysis.StoppedGeometricLogBound
import Universality.Percolation.ActualReliabilityExitLogBound
import Universality.Analysis.PowerResponseExponent

namespace Universality.Rule
noncomputable section
open FiniteNetwork Filter
open scoped Topology
set_option maxHeartbeats 0

/-- Exponent of the actual thermodynamic escaping mass. Identification with
percolation on a uniformly rooted infinite graph is a separate obligation. -/
theorem Classical.escaping_root_mass_exponent {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Tendsto (fun p : ℝ => Real.log (rule.escapingRootMass p) / Real.log (p - critical))
      (𝓝[>] critical)
      (𝓝 ((Real.log (rule.edges : ℝ) - Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)) /
        Real.log (deriv rule.network.reliability critical))) := by
  obtain ⟨massRadius, hmassRadius, _, _, hmass⟩ := h.escaping_root_mass_exit_bounds critical hc hc' hfixed
  obtain ⟨escapeRadius, hescapeRadius, _, _, hescape⟩ := h.reliability_exit_log_bound critical hc hc' hfixed
  let radius := min massRadius escapeRadius
  have hradius : 0 < radius := lt_min hmassRadius hescapeRadius
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := hmass radius hradius (min_le_left _ _)
  obtain ⟨bound, hbound, htime⟩ := hescape radius hradius (min_le_right _ _)
  have hedges : 0 < (rule.edges : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt h.edges_gt_one)
  have hgrowth : 0 < ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hmultiplier : 0 < Real.log (deriv rule.network.reliability critical) :=
    Real.log_pos (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale)
  have hnear : ∀ᶠ p in 𝓝[>] critical, |p - critical| < radius := by
    have ht : ContinuousAt (fun p : ℝ => |p - critical|) critical := by fun_prop
    have hv : |critical - critical| < radius := by simpa using hradius
    exact (ht.eventually (gt_mem_nhds hv)).filter_mono nhdsWithin_le_nhds
  have hunit : ∀ᶠ p in 𝓝[>] critical, p < 1 :=
    (gt_mem_nhds hc').filter_mono nhdsWithin_le_nhds
  have herror : ∀ᶠ p in 𝓝[>] critical,
      |Real.log (rule.escapingRootMass p) -
        (-Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / (rule.edges : ℝ)) / Real.log (deriv rule.network.reliability critical)) *
          (Real.log |p - critical|)| ≤
        |Real.log lower| + |Real.log upper| +
          |Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / (rule.edges : ℝ)) / Real.log (deriv rule.network.reliability critical)| * bound := by
    filter_upwards [hnear, hunit, self_mem_nhdsWithin] with p hpnear hpunit hpc
    have hpabove : critical < p := hpc
    have hb := hbounds p hpabove hpunit hpnear
    exact stopped_geometric_log_error (rule.escapingRootMass p) (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / (rule.edges : ℝ))
      (deriv rule.network.reliability critical) |p - critical| lower upper bound
      (rule.reliabilityExitTime critical radius p) (div_pos hgrowth hedges) hmultiplier.ne'
      hlower hupper hb.1 hb.2 (htime p (hc.trans hpabove) hpunit (ne_of_gt hpabove))
  have hlimit := tendsto_ratio_of_bounded_error (𝓝[>] critical)
    (fun p => Real.log (rule.escapingRootMass p)) (fun p => Real.log |p - critical|)
    _ _ (tendsto_log_abs_deviation_right critical) herror
  have hvalue : -Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / (rule.edges : ℝ)) / Real.log (deriv rule.network.reliability critical) =
      (Real.log (rule.edges : ℝ) - Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)) / Real.log (deriv rule.network.reliability critical) := by
    rw [Real.log_div hgrowth.ne' hedges.ne']
    ring
  rw [hvalue] at hlimit
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hpc : critical < p := hp
  rw [abs_of_pos (sub_pos.mpr hpc)]

end
end Universality.Rule
