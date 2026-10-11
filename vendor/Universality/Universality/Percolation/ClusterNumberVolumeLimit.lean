import Universality.Percolation.ClusterNumberNormalization

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open FiniteNetwork Filter
open scoped Topology

theorem generation_cluster_number_per_edge_tendsto (rule : Rule)
    (hedges : 1 < rule.edges) (p : Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedClusterNumber p.val /
      (rule.edges : ℝ) ^ (n + 1)) atTop
      (𝓝 (discountedIteration rule.network.unitReliability
        (fun q => rule.network.expectedInternalClusterNumber q.val) (1 / (rule.edges : ℝ)) p)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hnonneg : 0 ≤ 1 / (rule.edges : ℝ) := one_div_nonneg.mpr (lt_trans zero_lt_one hm).le
  have hless : 1 / (rule.edges : ℝ) < 1 := (div_lt_one (lt_trans zero_lt_one hm)).mpr hm
  have hpowers : Tendsto (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hless).comp (tendsto_add_atTop_nat 1)
  have horbit (n : ℕ) : 0 ≤ rule.network.reliability^[n] p.val ∧ rule.network.reliability^[n] p.val ≤ 1 := by
    rw [← rule.network.unitReliability_iterate_val]
    exact (rule.network.unitReliability^[n] p).property
  have hcorrection : Tendsto (fun n : ℕ =>
      (2 - rule.network.reliability^[n + 1] p.val) * (1 / (rule.edges : ℝ)) ^ (n + 1)) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n : ℕ => 2 * (1 / (rule.edges : ℝ)) ^ (n + 1))
    · intro n
      exact mul_nonneg (by linarith [(horbit (n + 1)).2]) (pow_nonneg hnonneg _)
    · intro n
      exact mul_le_mul_of_nonneg_right (by linarith [(horbit (n + 1)).1]) (pow_nonneg hnonneg _)
    · simpa using hpowers.const_mul 2
  have hsum := (discountedIteration_summable rule.network.unitReliability
    (fun q => rule.network.expectedInternalClusterNumber q.val) (1 / (rule.edges : ℝ)) (rule.vertices : ℝ)
    hnonneg hless (fun q => by
      rw [abs_of_nonneg (rule.network.expectedInternalClusterNumber_bounds q.property.1 q.property.2).1]
      exact (rule.network.expectedInternalClusterNumber_bounds q.property.1 q.property.2).2) p).hasSum.tendsto_sum_nat
  have hshift := hsum.comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, rule.network.unitReliability_iterate_val] at hshift
  simpa only [generation_expectedClusterNumber_normalized rule _ _ (by omega), add_zero,
    discountedIteration, rule.network.unitReliability_iterate_val] using hshift.add hcorrection

/-- Identification of the bounded series solution with the actual expected
cluster-number density, with the volume limit taken first. -/
theorem generation_cluster_number_density_tendsto (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) (p : Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedClusterNumber p.val /
      ((rule.generation n).vertices : ℝ)) atTop (𝓝 (rule.network.clusterNumberSeries p)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hne : (rule.edges : ℝ) ≠ 0 := (lt_trans zero_lt_one hm).ne'
  have h := (rule.generation_cluster_number_per_edge_tendsto hedges p).div
    (rule.generation_volume_ratio_tendsto hedges)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  have hquotient (n : ℕ) :
      ((rule.generation n).network.expectedClusterNumber p.val / (rule.edges : ℝ) ^ (n + 1)) /
        (((rule.generation n).vertices : ℝ) / (rule.edges : ℝ) ^ (n + 1)) =
      (rule.generation n).network.expectedClusterNumber p.val / ((rule.generation n).vertices : ℝ) := by
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ hne)]
  convert h using 1
  · ext n
    exact (hquotient n).symm
  · unfold clusterNumberSeries
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

end
end Universality.Rule
