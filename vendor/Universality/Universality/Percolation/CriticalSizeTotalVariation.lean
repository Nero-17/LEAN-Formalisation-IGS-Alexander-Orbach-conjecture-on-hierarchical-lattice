import Universality.Probability.DiscreteTotalVariation
import Universality.Percolation.CriticalBirthMass

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem uniformVertexClusterMassProbability_eq_zero (p : ℝ) (size : ℕ) (hsize : vertices < size) :
    R.uniformVertexClusterMassProbability p size = 0 := by
  have hcard (configuration : Configuration edges) (root : Fin vertices) :
      (R.clusterVertices configuration root).card ≠ size := by
    have hle : (R.clusterVertices configuration root).card ≤ vertices := by
      simpa using Finset.card_le_univ (R.clusterVertices configuration root)
    omega
  simp [uniformVertexClusterMassProbability, hcard]

theorem uniformVertexClusterMassProbability_hasSum (p : ℝ) :
    HasSum (R.uniformVertexClusterMassProbability p) 1 := by
  rw [← R.sum_uniformVertexClusterMassProbability p]
  apply hasSum_sum_of_ne_finset_zero
  intro size hsize
  apply R.uniformVertexClusterMassProbability_eq_zero
  simp only [Finset.mem_range] at hsize
  omega

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- The actual finite uniform-root size laws converge in total variation at
criticality. This is a statement about cluster-size laws, not a construction
of an infinite rooted graph. -/
theorem Classical.critical_cluster_size_total_variation {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    Tendsto (fun n : ℕ => ∑' size : ℕ,
      |(rule.generation n).network.uniformVertexClusterMassProbability p size -
        (size : ℝ) * (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
          rule.clusterSizeBirthSeries p size)|) atTop (𝓝 0) := by
  have hpointwise := rule.generation_uniformVertexClusterMassProbability_tendsto
    h.edges_gt_one h.vertices_gt_two hp.le hp'.le
  apply discrete_probability_total_variation atTop
    (fun n size => (rule.generation n).network.uniformVertexClusterMassProbability p size)
    (fun size => (size : ℝ) * (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
      rule.clusterSizeBirthSeries p size))
  · intro n size
    exact (rule.generation n).network.uniformVertexClusterMassProbability_nonneg hp.le hp'.le size
  · intro size
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hpointwise size) (Eventually.of_forall (fun n =>
      (rule.generation n).network.uniformVertexClusterMassProbability_nonneg hp.le hp'.le size))
  · intro n
    exact (rule.generation n).network.uniformVertexClusterMassProbability_hasSum p
  · exact h.critical_cluster_size_mass_hasSum p hp hp' hfixed
  · exact hpointwise

end
end Universality.Rule
