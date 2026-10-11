import Universality.Percolation.SubcriticalBirthMomentLower

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology ENNReal

theorem Classical.subcritical_root_moment_eq_top {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical)
    (order : ℕ)
    (hthreshold : (rule.edges : ℝ) ≤
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1)) :
    rule.limitingRootSizeMoment p order = ⊤ := by
  have hp' := hpc.trans hc'
  by_contra hfinite
  have hs := (rule.limitingRootSizeMoment_finite_iff_birth_summable
    h.edges_gt_one h.vertices_gt_two hp.le hp'.le order).mp hfinite
  obtain ⟨lower, hlower, hlowerBound⟩ :=
    h.subcritical_birth_moment_eventual_lower_bound critical p hc hc' hfixed hp hpc (order + 1) (by omega)
  have hm : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hratio : 1 ≤
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) /
        (rule.edges : ℝ) := (le_div_iff₀ hm).mpr (by simpa using hthreshold)
  have hzero := hs.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
  have hbound : ∀ᶠ n : ℕ in atTop,
      lower / (rule.edges : ℝ) ^ 2 ≤
        (1 / (rule.edges : ℝ)) ^ ((n + 1) + 1) *
          rule.expectedClusterBirthPower p (order + 1) (n + 1) := by
    filter_upwards [hlowerBound] with n hn
    calc
      lower / (rule.edges : ℝ) ^ 2 ≤ lower / (rule.edges : ℝ) ^ 2 *
          ((rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) /
            (rule.edges : ℝ)) ^ n := by
        exact le_mul_of_one_le_right (div_nonneg hlower.le (sq_nonneg _)) (one_le_pow₀ hratio)
      _ = (1 / (rule.edges : ℝ)) ^ ((n + 1) + 1) *
          (lower * (rule.network.fullGraph.degree rule.network.source : ℝ) ^
            ((order + 1) * n)) := by
        rw [pow_mul, div_pow]
        simp only [pow_succ, one_div_pow]
        field_simp [hm.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
  have hnonpos : lower / (rule.edges : ℝ) ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hzero hbound
  exact (div_pos hlower (sq_pos_of_pos hm)).not_ge hnonpos

end
end Universality.Rule
