import Universality.Percolation.CriticalBirthSizeSeriesBounds

namespace Universality.Rule
noncomputable section

theorem Classical.critical_root_size_probability_scale_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∃ start : ℕ,
      ∀ depth : ℕ, start ≤ depth → ∀ size : ℕ, rule.vertices < size →
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth ≤ (size : ℝ) →
      (size : ℝ) ≤ ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (depth + 1) →
      lower * ((size : ℝ) * (1 / ((rule.edges : ℝ) * (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) ^ depth) ≤
        rule.limitingRootSizeProbability p size ∧
      rule.limitingRootSizeProbability p size ≤
        upper * ((size : ℝ) * (1 / ((rule.edges : ℝ) * (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) ^ depth) := by
  obtain ⟨lower, upper, hlower, hupper, start, hb⟩ := h.critical_birth_size_series_scale_bounds p hp hp' hfixed
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  have hfactor : 0 < ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) :=
    div_pos (sub_pos.mpr hm) (sub_pos.mpr hv)
  refine ⟨(((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) * lower,
    (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) * upper,
    mul_pos hfactor hlower, mul_pos hfactor hupper, start, ?_⟩
  intro depth hdepth size hsize hlow hhigh
  have hh := hb depth hdepth size hsize hlow hhigh
  constructor
  · have ht := mul_le_mul_of_nonneg_left hh.1 (mul_nonneg (Nat.cast_nonneg size) hfactor.le)
    unfold limitingRootSizeProbability
    nlinarith only [ht]
  · have ht := mul_le_mul_of_nonneg_left hh.2 (mul_nonneg (Nat.cast_nonneg size) hfactor.le)
    unfold limitingRootSizeProbability
    nlinarith only [ht]

end
end Universality.Rule
