import Universality.Percolation.BirthExpectations
import Universality.Graph.VolumeLimit

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open Filter
open scoped Topology

/-- Birth generation zero is the first rule itself; later generations count
actual internal clusters touching a vertex of the top rule. -/
def expectedClusterBirth (rule : Rule) (p : ℝ) (size : ℕ) : ℕ → ℝ
  | 0 => rule.network.expectedInternalClusterCount p size
  | n + 1 => rule.network.expectedBirthClusterCount (rule.generation n).network p size

theorem expectedClusterBirth_bounds (rule : Rule) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (size n : ℕ) :
    0 ≤ rule.expectedClusterBirth p size n ∧ rule.expectedClusterBirth p size n ≤ rule.vertices := by
  cases n with
  | zero => exact rule.network.expectedInternalClusterCount_bounds hp hp' size
  | succ n => exact rule.network.expectedBirthClusterCount_bounds _ hp hp' size

theorem generation_internal_count_normalized (rule : Rule) (hedges : 0 < rule.edges)
    (p : ℝ) (size n : ℕ) :
    (rule.generation n).network.expectedInternalClusterCount p size / (rule.edges : ℝ) ^ (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (1 / (rule.edges : ℝ)) ^ (k + 1) * rule.expectedClusterBirth p size k := by
  have hm : (rule.edges : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hedges
  induction n with
  | zero => simp [generation, expectedClusterBirth, div_eq_mul_inv, mul_comm]
  | succ n ih =>
    rw [generation_expectedInternalClusterCount, Finset.sum_range_succ, ← ih]
    simp only [expectedClusterBirth, pow_succ, one_div_pow]
    field_simp
    <;> ring

def clusterSizeBirthSeries (rule : Rule) (p : ℝ) (size : ℕ) : ℝ :=
  ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedClusterBirth p size n

theorem clusterSizeBirthSeries_summable (rule : Rule) (hedges : 1 < rule.edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedClusterBirth p size n) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hd : 0 ≤ 1 / (rule.edges : ℝ) := by positivity
  have hd' : 1 / (rule.edges : ℝ) < 1 := (div_lt_one (lt_trans zero_lt_one hm)).mpr hm
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.vertices)
    (((summable_geometric_of_lt_one hd hd').comp_injective
      (fun a b (h : a + 1 = b + 1) => Nat.add_right_cancel h)).mul_right (rule.vertices : ℝ))
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hd _),
    abs_of_nonneg (rule.expectedClusterBirth_bounds hp hp' size n).1]
  exact mul_le_mul_of_nonneg_left (rule.expectedClusterBirth_bounds hp hp' size n).2 (pow_nonneg hd _)

theorem generation_internal_count_per_edge_tendsto (rule : Rule) (hedges : 1 < rule.edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalClusterCount p size /
      (rule.edges : ℝ) ^ (n + 1)) atTop (𝓝 (rule.clusterSizeBirthSeries p size)) := by
  have h := (rule.clusterSizeBirthSeries_summable hedges hp hp' size).hasSum.tendsto_sum_nat
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, ← rule.generation_internal_count_normalized (by omega) p size,
    clusterSizeBirthSeries] using hshift

theorem generation_internal_cluster_density_tendsto (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalClusterCount p size /
      ((rule.generation n).vertices : ℝ)) atTop
      (𝓝 (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) * rule.clusterSizeBirthSeries p size)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hne : (rule.edges : ℝ) ≠ 0 := (lt_trans zero_lt_one hm).ne'
  have h := (rule.generation_internal_count_per_edge_tendsto hedges hp hp' size).div
    (rule.generation_volume_ratio_tendsto hedges)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  have hquotient (n : ℕ) :
      ((rule.generation n).network.expectedInternalClusterCount p size / (rule.edges : ℝ) ^ (n + 1)) /
        (((rule.generation n).vertices : ℝ) / (rule.edges : ℝ) ^ (n + 1)) =
      (rule.generation n).network.expectedInternalClusterCount p size / ((rule.generation n).vertices : ℝ) := by
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ hne)]
  convert h using 1
  · ext n
    exact (hquotient n).symm
  · congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

end
end Universality.Rule
