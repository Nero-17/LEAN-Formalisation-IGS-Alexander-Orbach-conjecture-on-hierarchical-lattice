import Universality.Percolation.SubcriticalBoundaryMeanLimit
import Universality.Percolation.RootedLimitBoundaryMass
import Universality.Percolation.CriticalSizeTotalVariation

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.subcritical_escapingRootMass_zero {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    rule.escapingRootMass p = 0 := by
  obtain ⟨limit, hpositive, hlimit⟩ := h.subcritical_boundary_mean_limit critical p hc hc' hfixed hp hpc
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hmpos : (0 : ℝ) < rule.edges := lt_trans zero_lt_one hm
  have hd : (0 : ℝ) < rule.network.fullGraph.degree rule.network.source := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    have hd := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 0 < rule.network.sourceIncidentEdges.card)
  have hdegree : (rule.network.fullGraph.degree rule.network.source : ℝ) < rule.edges := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    exact_mod_cast rule.network.sourceIncidentEdges_card_lt_edges (h.connected _) h.scale
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hmpos.le)
    ((div_lt_one hmpos).mpr hdegree)
  have hmass : Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalBoundaryMass p /
      (rule.edges : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    have hb := (hlimit.mul hgeom).div_const (rule.edges : ℝ)
    simp only [mul_zero, zero_div] at hb
    convert hb using 1
    ext n
    rw [div_pow, pow_succ]
    field_simp [hd.ne', hmpos.ne']
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  have hquotient := hmass.div (rule.generation_volume_ratio_tendsto h.edges_gt_one)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  simp only [zero_div] at hquotient
  have hzero : Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalBoundaryMass p /
      ((rule.generation n).vertices : ℝ)) atTop (𝓝 0) := by
    convert hquotient using 1
    ext n
    change _ = ((rule.generation n).network.expectedInternalBoundaryMass p / (rule.edges : ℝ) ^ (n + 1)) / (((rule.generation n).vertices : ℝ) / (rule.edges : ℝ) ^ (n + 1))
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ hmpos.ne')]
  exact tendsto_nhds_unique
    (rule.generation_boundary_mass_density_limit h.edges_gt_one h.vertices_gt_two hp.le (hpc.trans hc').le) hzero


/-- Positive-subcritical actual finite uniform-root cluster-size laws converge
in total variation to the normalized limiting size law. -/
theorem Classical.subcritical_cluster_size_total_variation {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    Tendsto (fun n : ℕ => ∑' size : ℕ,
      |(rule.generation n).network.uniformVertexClusterMassProbability p size -
        rule.limitingRootSizeProbability p size|) atTop (𝓝 0) := by
  have hp' := hpc.trans hc'
  apply discrete_probability_total_variation atTop
    (fun n size => (rule.generation n).network.uniformVertexClusterMassProbability p size)
    (rule.limitingRootSizeProbability p)
  · intro n size
    exact (rule.generation n).network.uniformVertexClusterMassProbability_nonneg hp.le hp'.le size
  · exact rule.limitingRootSizeProbability_nonneg h.edges_gt_one h.vertices_gt_two hp.le hp'.le
  · intro n
    exact (rule.generation n).network.uniformVertexClusterMassProbability_hasSum p
  · have hs := (rule.limitingRootSizeProbability_summable h.edges_gt_one h.vertices_gt_two hp.le hp'.le).hasSum
    have hz := h.subcritical_escapingRootMass_zero critical p hc hc' hfixed hp hpc
    unfold escapingRootMass at hz
    have hone : ∑' size, rule.limitingRootSizeProbability p size = 1 := by linarith
    rwa [hone] at hs
  · exact rule.generation_uniformVertexClusterMassProbability_tendsto h.edges_gt_one h.vertices_gt_two hp.le hp'.le

end
end Universality.Rule

