import Universality.Percolation.BirthSeries

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def expectedClusterCount (p : ℝ) (size : ℕ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * R.clusterCount configuration size

theorem expectedClusterCount_boundary_bounds {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    0 ≤ R.expectedClusterCount p size - R.expectedInternalClusterCount p size ∧
      R.expectedClusterCount p size - R.expectedInternalClusterCount p size ≤ 2 := by
  have hlower : R.expectedInternalClusterCount p size ≤ R.expectedClusterCount p size := by
    apply Finset.sum_le_sum
    intro configuration _
    apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
    exact_mod_cast (R.internalClusterCount_bounds configuration size).1
  have hupper : R.expectedClusterCount p size ≤ R.expectedInternalClusterCount p size + 2 := by
    calc
      _ ≤ ∑ configuration, bernoulliWeight p configuration *
          ((R.internalClusterCount configuration size : ℝ) + 2) := by
        apply Finset.sum_le_sum
        intro configuration _
        apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
        exact_mod_cast (R.internalClusterCount_bounds configuration size).2
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_bernoulliWeight, one_mul]
        rfl
  exact ⟨sub_nonneg.mpr hlower, by linarith⟩

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open Filter
open scoped Topology

theorem generation_cluster_count_per_edge_tendsto (rule : Rule) (hedges : 1 < rule.edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedClusterCount p size /
      (rule.edges : ℝ) ^ (n + 1)) atTop (𝓝 (rule.clusterSizeBirthSeries p size)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hpos : 0 < (rule.edges : ℝ) := lt_trans zero_lt_one hm
  have hpowers : Tendsto (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (one_div_nonneg.mpr hpos.le)
      ((div_lt_one hpos).mpr hm)).comp (tendsto_add_atTop_nat 1)
  have hcorrection : Tendsto (fun n : ℕ =>
      ((rule.generation n).network.expectedClusterCount p size -
        (rule.generation n).network.expectedInternalClusterCount p size) / (rule.edges : ℝ) ^ (n + 1))
      atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n : ℕ => 2 * (1 / (rule.edges : ℝ)) ^ (n + 1))
    · intro n
      exact div_nonneg ((rule.generation n).network.expectedClusterCount_boundary_bounds hp hp' size).1
        (pow_nonneg hpos.le _)
    · intro n
      simpa only [one_div_pow, mul_one_div] using
        div_le_div_of_nonneg_right ((rule.generation n).network.expectedClusterCount_boundary_bounds hp hp' size).2
          (pow_nonneg hpos.le (n + 1))
    · simpa using hpowers.const_mul 2
  have h := (rule.generation_internal_count_per_edge_tendsto hedges hp hp' size).add hcorrection
  simpa only [← add_div, add_sub_cancel, add_zero] using h

/-- The actual finite-volume density of clusters of each fixed size converges
to the birth series with the graph's vertex normalization. -/
theorem generation_finiteClusterDensity_tendsto (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.finiteClusterDensity p size) atTop
      (𝓝 (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) * rule.clusterSizeBirthSeries p size)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hne : (rule.edges : ℝ) ≠ 0 := (lt_trans zero_lt_one hm).ne'
  have h := (rule.generation_cluster_count_per_edge_tendsto hedges hp hp' size).div
    (rule.generation_volume_ratio_tendsto hedges)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  have hquotient (n : ℕ) :
      ((rule.generation n).network.expectedClusterCount p size / (rule.edges : ℝ) ^ (n + 1)) /
        (((rule.generation n).vertices : ℝ) / (rule.edges : ℝ) ^ (n + 1)) =
      (rule.generation n).network.finiteClusterDensity p size := by
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ hne)]
    rfl
  convert h using 1
  · ext n
    exact (hquotient n).symm
  · congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

theorem generation_uniformVertexClusterMassProbability_tendsto (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.uniformVertexClusterMassProbability p size) atTop
      (𝓝 ((size : ℝ) * (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
        rule.clusterSizeBirthSeries p size))) := by
  simpa only [FiniteNetwork.uniformVertexClusterMassProbability_eq] using
    (rule.generation_finiteClusterDensity_tendsto hedges hvertices hp hp' size).const_mul (size : ℝ)

end
end Universality.Rule
