import Universality.Percolation.ClusterNumberVolumeLimit
import Universality.Percolation.ClusterSizeDensity

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem sum_clusterCount_cutoff (configuration : Configuration edges) (cutoff : ℕ) :
    (∑ size ∈ Finset.range cutoff, (R.clusterCount configuration size : ℝ)) =
      ∑ cluster ∈ R.clusterFamily configuration, if cluster.card < cutoff then (1 : ℝ) else 0 := by
  classical
  simp only [clusterCount, ← Finset.sum_boole]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cluster _
  simp

theorem clusterCount_cutoff_bounds (configuration : Configuration edges)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) :
    0 ≤ (R.clusterFamily configuration).card -
      ∑ size ∈ Finset.range cutoff, (R.clusterCount configuration size : ℝ) ∧
    (R.clusterFamily configuration).card -
      ∑ size ∈ Finset.range cutoff, (R.clusterCount configuration size : ℝ) ≤
        (vertices : ℝ) / cutoff := by
  classical
  rw [R.sum_clusterCount_cutoff]
  have heq : (R.clusterFamily configuration).card -
      (∑ cluster ∈ R.clusterFamily configuration, if cluster.card < cutoff then (1 : ℝ) else 0) =
      ∑ cluster ∈ R.clusterFamily configuration, if cutoff ≤ cluster.card then (1 : ℝ) else 0 := by
    have hcard : ((R.clusterFamily configuration).card : ℝ) =
        ∑ _cluster ∈ R.clusterFamily configuration, (1 : ℝ) := by simp
    rw [hcard, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro cluster _
    split_ifs <;> simp_all <;> omega
  rw [heq]
  refine ⟨Finset.sum_nonneg (fun _ _ => by positivity), ?_⟩
  rw [← R.sum_cluster_card configuration, Finset.sum_div]
  apply Finset.sum_le_sum
  intro cluster _
  split_ifs with h
  · apply (le_div_iff₀ (by exact_mod_cast hcutoff : (0 : ℝ) < cutoff)).mpr
    simpa using (show (cutoff : ℝ) ≤ cluster.card by exact_mod_cast h)
  · positivity

theorem finiteClusterDensity_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    0 ≤ R.finiteClusterDensity p size := by
  unfold finiteClusterDensity
  exact div_nonneg (Finset.sum_nonneg fun configuration _ =>
    mul_nonneg (bernoulliWeight_nonneg hp hp' configuration) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)

/-- The contribution of clusters beyond a size cutoff is uniformly bounded,
independently of the finite graph and the percolation parameter. -/
theorem finiteClusterDensity_cutoff_bounds {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) :
    (∑ size ∈ Finset.range cutoff, R.finiteClusterDensity p size) ≤
      R.expectedClusterNumber p / vertices ∧
    R.expectedClusterNumber p / vertices ≤
      (∑ size ∈ Finset.range cutoff, R.finiteClusterDensity p size) + 1 / cutoff := by
  have hvertices : (0 : ℝ) < vertices := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) R.two_le_vertices)
  have heq : R.expectedClusterNumber p / vertices -
      (∑ size ∈ Finset.range cutoff, R.finiteClusterDensity p size) =
      (∑ configuration, bernoulliWeight p configuration *
        ((R.clusterFamily configuration).card -
          ∑ size ∈ Finset.range cutoff, (R.clusterCount configuration size : ℝ))) / vertices := by
    simp only [expectedClusterNumber, finiteClusterDensity, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [← sub_div, ← Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]
  have hlo : 0 ≤ R.expectedClusterNumber p / vertices -
      (∑ size ∈ Finset.range cutoff, R.finiteClusterDensity p size) := by
    rw [heq]
    exact div_nonneg (Finset.sum_nonneg fun configuration _ =>
      mul_nonneg (bernoulliWeight_nonneg hp hp' configuration)
        (R.clusterCount_cutoff_bounds configuration cutoff hcutoff).1) hvertices.le
  have hhi : R.expectedClusterNumber p / vertices -
      (∑ size ∈ Finset.range cutoff, R.finiteClusterDensity p size) ≤ 1 / cutoff := by
    rw [heq]
    calc
      _ ≤ (∑ configuration : Configuration edges,
          bernoulliWeight p configuration * ((vertices : ℝ) / cutoff)) / vertices := by
        apply div_le_div_of_nonneg_right _ hvertices.le
        exact Finset.sum_le_sum fun configuration _ =>
          mul_le_mul_of_nonneg_left (R.clusterCount_cutoff_bounds configuration cutoff hcutoff).2
            (bernoulliWeight_nonneg hp hp' configuration)
      _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]; field_simp
  exact ⟨by linarith, by linarith⟩

end
end Universality.FiniteNetwork
