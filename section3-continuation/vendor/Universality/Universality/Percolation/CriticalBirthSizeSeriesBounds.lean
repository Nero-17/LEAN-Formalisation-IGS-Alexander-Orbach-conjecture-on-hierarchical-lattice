import Universality.Analysis.WeightedSizeSeries
import Universality.Percolation.CoarseRootPointTail
import Universality.Percolation.ActualBirthPointLower
import Universality.Percolation.ClusterMassSizeSums
import Universality.Percolation.RootedLimitSizeLaw

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 0

/-- The actual birth series at criticality on each spatial scale. The
initial rule contribution is removed using its finite support, explicitly. -/
theorem Classical.critical_birth_size_series_scale_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∃ start : ℕ,
      ∀ depth : ℕ, start ≤ depth → ∀ size : ℕ, rule.vertices < size →
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth ≤ (size : ℝ) →
      (size : ℝ) ≤ ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (depth + 1) →
      lower * (1 / ((rule.edges : ℝ) * (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) ^ depth ≤
        rule.clusterSizeBirthSeries p size ∧
      rule.clusterSizeBirthSeries p size ≤
        upper * (1 / ((rule.edges : ℝ) * (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) ^ depth := by
  let growth : ℝ := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hgrowth : 1 < growth :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hr : 0 < growth := zero_lt_one.trans hgrowth
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hmpos : (0 : ℝ) < rule.edges := zero_lt_one.trans hm
  have hproduct : 1 < (rule.edges : ℝ) * growth := hm.trans_le (le_mul_of_one_le_right hmpos.le hgrowth.le)
  obtain ⟨order, _, horder⟩ := exists_nat_pow_near hproduct.le hgrowth
  obtain ⟨upper, hupper, hu⟩ := h.birth_mass_polynomial_point_tail p hp hp' hfixed (order + 1) (by omega)
  obtain ⟨lower, hlower, hl⟩ := h.birth_mass_point_lower p hp hp' hfixed
  obtain ⟨start, hstart⟩ := eventually_atTop.mp hl
  have hfirst : (rule.edges : ℝ) * growth / growth ^ (order + 1) < 1 := (div_lt_one (pow_pos hr _)).mpr horder
  have hlater : 1 / ((rule.edges : ℝ) * growth) < 1 := (div_lt_one (mul_pos hmpos hr)).mpr hproduct
  refine ⟨lower / (rule.edges : ℝ) ^ 2,
    (upper / (rule.edges : ℝ) ^ 2) *
      ((1 - (rule.edges : ℝ) * growth / growth ^ (order + 1))⁻¹ + (1 - 1 / ((rule.edges : ℝ) * growth))⁻¹),
    div_pos hlower (pow_pos hmpos _),
    mul_pos (div_pos hupper (pow_pos hmpos _))
      (add_pos (inv_pos.mpr (sub_pos.mpr hfirst)) (inv_pos.mpr (sub_pos.mpr hlater))), start, ?_⟩
  intro depth hdepth size hsizeLarge hsizeLower hsizeUpper
  have hlocal := hstart depth hdepth size
    ((le_div_iff₀ (pow_pos hr _)).mpr (by simpa only [one_mul] using hsizeLower))
    ((div_le_iff₀ (pow_pos hr _)).mpr (by simpa only [pow_succ', mul_comm] using hsizeUpper))
  have hnumeric := weighted_size_series_bounds
    (fun n => rule.network.expectedBirthClusterCount (rule.generation n).network p size)
    (rule.edges : ℝ) growth (size : ℝ) upper lower hm hgrowth (order + 1) depth horder hsizeLower hupper.le
    (fun n => (rule.network.expectedBirthClusterCount_bounds (rule.generation n).network hp.le hp'.le size).1)
    (fun n => by simpa only [one_div_pow, mul_one_div] using hu n size)
    (by simpa only [one_div_pow, mul_one_div] using hlocal)
  have hseries : rule.clusterSizeBirthSeries p size =
      ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) *
        rule.network.expectedBirthClusterCount (rule.generation n).network p size := by
    unfold clusterSizeBirthSeries
    rw [(rule.clusterSizeBirthSeries_summable h.edges_gt_one hp.le hp'.le size).tsum_eq_zero_add]
    simp only [zero_add, pow_one, expectedClusterBirth,
      rule.network.expectedInternalClusterCount_eq_zero p size hsizeLarge, mul_zero, zero_add]
  rw [hseries]
  exact hnumeric.2

end
end Universality.Rule
