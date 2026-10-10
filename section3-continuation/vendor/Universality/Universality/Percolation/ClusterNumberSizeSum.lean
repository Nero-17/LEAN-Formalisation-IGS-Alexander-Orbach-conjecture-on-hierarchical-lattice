import Universality.Percolation.ClusterCountCutoff
import Universality.Analysis.UniformCountTailLimit
import Universality.Percolation.RootedLimitSizeLaw

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem clusterNumberSeries_hasSum_size_densities (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) (p : Set.Icc (0 : ℝ) 1) :
    HasSum (fun size => ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
      rule.clusterSizeBirthSeries p size) (rule.network.clusterNumberSeries p) := by
  apply hasSum_of_uniform_count_tails
    (fun n size => (rule.generation n).network.finiteClusterDensity p size) _
    (fun n => (rule.generation n).network.expectedClusterNumber p / (rule.generation n).vertices) _
  · exact fun n size => (rule.generation n).network.finiteClusterDensity_nonneg p.property.1 p.property.2 size
  · exact fun size => rule.generation_finiteClusterDensity_tendsto hedges hvertices p.property.1 p.property.2 size
  · exact rule.generation_cluster_number_density_tendsto hedges hvertices p
  · exact fun n cutoff hcutoff => (rule.generation n).network.finiteClusterDensity_cutoff_bounds
      p.property.1 p.property.2 cutoff hcutoff

/-- The zero-size density vanishes because every actual finite cluster contains
at least one vertex. -/
theorem clusterSizeBirthSeries_zero (rule : Rule) (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) * rule.clusterSizeBirthSeries p 0 = 0 := by
  have hzero (n : ℕ) : (rule.generation n).network.finiteClusterDensity p 0 = 0 := by
    unfold FiniteNetwork.finiteClusterDensity FiniteNetwork.clusterCount
    have hempty (configuration) :
        ((rule.generation n).network.clusterFamily configuration).filter
          (fun cluster => cluster.card = 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro cluster hcluster hcard
      have := (rule.generation n).network.cluster_card_pos configuration cluster hcluster
      omega
    simp only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero, Finset.sum_const_zero, zero_div]
  apply tendsto_nhds_unique (rule.generation_finiteClusterDensity_tendsto hedges hvertices hp hp' 0)
  simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem clusterNumberSeries_hasSum_root_size_quotients (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices) (p : Set.Icc (0 : ℝ) 1) :
    HasSum (fun size => rule.limitingRootSizeProbability p size / (size : ℝ))
      (rule.network.clusterNumberSeries p) := by
  convert rule.clusterNumberSeries_hasSum_size_densities hedges hvertices p using 1
  funext size
  by_cases hzero : size = 0
  · subst size
    simp [rule.clusterSizeBirthSeries_zero hedges hvertices p.property.1 p.property.2]
  · unfold limitingRootSizeProbability
    have hne : (size : ℝ) ≠ 0 := by exact_mod_cast hzero
    field_simp

end
end Universality.Rule
