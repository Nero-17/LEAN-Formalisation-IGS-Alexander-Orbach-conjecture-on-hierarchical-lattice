import Universality.Percolation.AnnealedBirthMomentLower

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology ENNReal

/-- At criticality, the actual limiting uniform-root finite-cluster moment
diverges when the corresponding mass growth power reaches the edge volume
growth, including the equality case. -/
theorem Classical.critical_root_moment_eq_top {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ)
    (hthreshold : (rule.edges : ℝ) ≤
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order + 1)) :
    rule.limitingRootSizeMoment p order = ⊤ := by
  by_contra hfinite
  have hs := (rule.limitingRootSizeMoment_finite_iff_birth_summable
    h.edges_gt_one h.vertices_gt_two hp.le hp'.le order).mp hfinite
  obtain ⟨lower, hlower, hlowerBound⟩ :=
    h.birth_moment_eventual_lower_bound p hp hp' hfixed (order + 1) (by omega)
  have hm : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hratio : 1 ≤
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order + 1) /
        (rule.edges : ℝ) := (le_div_iff₀ hm).mpr (by simpa using hthreshold)
  have hzero := hs.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
  have hbound : ∀ᶠ n : ℕ in atTop,
      lower / (rule.edges : ℝ) ^ 2 ≤
        (1 / (rule.edges : ℝ)) ^ ((n + 1) + 1) *
          rule.expectedClusterBirthPower p (order + 1) (n + 1) := by
    filter_upwards [hlowerBound] with n hn
    calc
      lower / (rule.edges : ℝ) ^ 2 ≤ lower / (rule.edges : ℝ) ^ 2 *
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order + 1) /
            (rule.edges : ℝ)) ^ n := by
        exact le_mul_of_one_le_right (div_nonneg hlower.le (sq_nonneg _)) (one_le_pow₀ hratio)
      _ = (1 / (rule.edges : ℝ)) ^ ((n + 1) + 1) *
          (lower * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^
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
