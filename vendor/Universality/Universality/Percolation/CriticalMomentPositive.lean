import Universality.Percolation.RealAnnealedMoment
import Universality.Percolation.AnnealedBirthMomentLower
import Universality.Percolation.AnnealedCriticalMomentFinite

namespace Universality.Rule
noncomputable section

theorem Classical.critical_root_moment_toReal_pos {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) < rule.edges) :
    0 < (rule.limitingRootSizeMoment critical order).toReal := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  have hmpos : (0 : ℝ) < rule.edges := zero_lt_one.trans hm
  have hgrowth : 0 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).1.trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hfinite := h.critical_root_moment_ne_top critical hc hc' hfixed order hthreshold
  have hs := (rule.limitingRootSizeMoment_finite_iff_birth_summable
    h.edges_gt_one h.vertices_gt_two hc.le hc'.le order).mp hfinite
  obtain ⟨lower, hlower, hevent⟩ := h.birth_moment_eventual_lower_bound critical hc hc' hfixed (order + 1) (by omega)
  obtain ⟨n, hn⟩ := hevent.exists
  have hterm : 0 < (1 / (rule.edges : ℝ)) ^ ((n + 1) + 1) * rule.expectedClusterBirthPower critical (order + 1) (n + 1) :=
    mul_pos (pow_pos (one_div_pos.mpr hmpos) _) ((mul_pos hlower (pow_pos hgrowth _)).trans_le hn)
  rw [rule.limitingRootSizeMoment_toReal_birth_series h.edges_gt_one h.vertices_gt_two hc.le hc'.le order hfinite]
  apply mul_pos (div_pos (sub_pos.mpr hm) (sub_pos.mpr hv))
  apply hterm.trans_le
  simpa only [Finset.sum_singleton] using hs.sum_le_tsum {n + 1} (fun i _ =>
    mul_nonneg (pow_nonneg (one_div_nonneg.mpr hmpos.le) _) (rule.expectedClusterBirthPower_nonneg hc.le hc'.le _ _))

end
end Universality.Rule
