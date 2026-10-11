import Universality.Percolation.ClusterMassSizeSums

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped Topology

theorem generation_internal_mass_birth_sum (rule : Rule) (hedges : 0 < rule.edges) (p : ℝ) (n : ℕ) :
    (rule.generation n).network.expectedInternalClusterMass p / (rule.edges : ℝ) ^ (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (1 / (rule.edges : ℝ)) ^ (k + 1) *
        ∑' size : ℕ, (size : ℝ) * rule.expectedClusterBirth p size k := by
  calc
    _ = ∑' size : ℕ, ((size : ℝ) *
        (rule.generation n).network.expectedInternalClusterCount p size) / (rule.edges : ℝ) ^ (n + 1) :=
      ((rule.generation n).network.hasSum_size_expectedInternalClusterCount p).div_const _ |>.tsum_eq.symm
    _ = ∑' size : ℕ, ∑ k ∈ Finset.range (n + 1),
        (1 / (rule.edges : ℝ)) ^ (k + 1) * ((size : ℝ) * rule.expectedClusterBirth p size k) := by
      apply tsum_congr
      intro size
      rw [mul_div_assoc, rule.generation_internal_count_normalized hedges p size n, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k ∈ Finset.range (n + 1), ∑' size : ℕ,
        (1 / (rule.edges : ℝ)) ^ (k + 1) * ((size : ℝ) * rule.expectedClusterBirth p size k) := by
      apply Summable.tsum_finsetSum
      intro k _
      exact (rule.expectedClusterBirth_size_summable p k).mul_left _
    _ = _ := by simp only [tsum_mul_left]

theorem Classical.critical_birth_mass_hasSum {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    HasSum (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1) *
      ∑' size : ℕ, (size : ℝ) * rule.expectedClusterBirth p size n)
      (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) := by
  have hnonneg (n : ℕ) : 0 ≤ (1 / (rule.edges : ℝ)) ^ (n + 1) *
      ∑' size : ℕ, (size : ℝ) * rule.expectedClusterBirth p size n :=
    mul_nonneg (pow_nonneg (by positivity) _) (tsum_nonneg (fun size =>
      mul_nonneg (Nat.cast_nonneg _) (rule.expectedClusterBirth_bounds hp.le hp'.le size n).1))
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hlimit := (h.internal_cluster_mass_density_tendsto_one p hp hp' hfixed).mul
    (rule.generation_volume_ratio_tendsto h.edges_gt_one)
  simp only [one_mul] at hlimit
  convert hlimit using 1
  ext n
  rw [← rule.generation_internal_mass_birth_sum (by have := h.edges_gt_one; omega) p n]
  have hv : ((rule.generation n).vertices : ℝ) ≠ 0 := by
    have htwo := (rule.generation n).network.two_le_vertices
    exact_mod_cast (by omega : (rule.generation n).vertices ≠ 0)
  field_simp [hv]

theorem Classical.critical_cluster_size_mass_hasSum {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    HasSum (fun size : ℕ => (size : ℝ) *
      (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) * rule.clusterSizeBirthSeries p size)) 1 := by
  have hnonneg (pair : ℕ × ℕ) : 0 ≤
      (1 / (rule.edges : ℝ)) ^ (pair.1 + 1) *
        ((pair.2 : ℝ) * rule.expectedClusterBirth p pair.2 pair.1) := by
    exact mul_nonneg (pow_nonneg (by positivity) _) (mul_nonneg (Nat.cast_nonneg _)
      (rule.expectedClusterBirth_bounds hp.le hp'.le _ _).1)
  have htotal := h.critical_birth_mass_hasSum p hp hp' hfixed
  have hdouble : Summable (fun pair : ℕ × ℕ => (1 / (rule.edges : ℝ)) ^ (pair.1 + 1) *
      ((pair.2 : ℝ) * rule.expectedClusterBirth p pair.2 pair.1)) := by
    apply (summable_prod_of_nonneg hnonneg).mpr
    constructor
    · intro n
      simpa only [] using (rule.expectedClusterBirth_size_summable p n).mul_left
        ((1 / (rule.edges : ℝ)) ^ (n + 1))
    · simpa only [tsum_mul_left] using htotal.summable
  have hsize : HasSum (fun size : ℕ => (size : ℝ) * rule.clusterSizeBirthSeries p size)
      (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) := by
    have hs := hdouble.prod_symm.prod.hasSum
    have hswap := Summable.tsum_comm (f := fun n size : ℕ =>
      (1 / (rule.edges : ℝ)) ^ (n + 1) * ((size : ℝ) * rule.expectedClusterBirth p size n)) hdouble
    have heq (size : ℕ) :
        (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 1) *
          ((size : ℝ) * rule.expectedClusterBirth p size n)) = (size : ℝ) * rule.clusterSizeBirthSeries p size := by
      unfold clusterSizeBirthSeries
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    simp only [Prod.swap_prod_mk, heq] at hs hswap
    simp only [tsum_mul_left] at hswap
    rw [htotal.tsum_eq] at hswap
    rw [hswap] at hs
    exact hs
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  have hscale := hsize.mul_left (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2))
  have hcancel : ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
      (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) = 1 := by
    field_simp [(sub_pos.mpr hm).ne', (sub_pos.mpr hv).ne']
  rw [hcancel] at hscale
  exact hscale.congr_fun (fun size => by ring)

end
end Universality.Rule
