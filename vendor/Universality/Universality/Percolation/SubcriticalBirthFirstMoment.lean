import Universality.Percolation.SubcriticalBoundaryMeanLimit

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology ENNReal

theorem Classical.subcritical_birth_first_moment_limit {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    ∃ limit : ℝ, 0 < limit ∧ Tendsto (fun n : ℕ =>
      rule.expectedClusterBirthPower p 1 (n + 1) /
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n)
      atTop (𝓝 limit) := by
  obtain ⟨limit, hpositive, hlimit⟩ := h.subcritical_boundary_mean_limit critical p hc hc' hfixed hp hpc
  have hradius : 1 < (rule.network.fullGraph.degree rule.network.source : ℝ) := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    have hd := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 1 < rule.network.sourceIncidentEdges.card)
  have hdegree : (rule.network.fullGraph.degree rule.network.source : ℝ) < rule.edges := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    exact_mod_cast rule.network.sourceIncidentEdges_card_lt_edges (h.connected _) h.scale
  have hne : (rule.network.fullGraph.degree rule.network.source : ℝ) ≠ 0 :=
    (lt_trans zero_lt_one hradius).ne'
  refine ⟨((rule.edges : ℝ) -
    (rule.network.fullGraph.degree rule.network.source : ℝ)) * limit,
    mul_pos (sub_pos.mpr hdegree) hpositive, ?_⟩
  have hconstant : Tendsto (fun n : ℕ => ((rule.vertices : ℝ) - 2) /
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa only [one_div_pow, mul_one_div, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (one_div_nonneg.mpr (lt_trans zero_lt_one hradius).le)
        ((div_lt_one (lt_trans zero_lt_one hradius)).mpr hradius)).const_mul ((rule.vertices : ℝ) - 2)
  have hnext := (hlimit.comp (tendsto_add_atTop_nat 1)).const_mul
    (rule.network.fullGraph.degree rule.network.source : ℝ)
  have hs := (hconstant.add (hlimit.const_mul (rule.edges : ℝ))).sub hnext
  have heq (n : ℕ) : rule.expectedClusterBirthPower p 1 (n + 1) /
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n =
      ((rule.vertices : ℝ) - 2) /
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n +
        (rule.edges : ℝ) * ((rule.generation n).network.expectedInternalBoundaryMass p /
          (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n) -
        (rule.network.fullGraph.degree rule.network.source : ℝ) *
          ((rule.generation (n + 1)).network.expectedInternalBoundaryMass p /
            (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (n + 1)) := by
    rw [rule.expectedClusterBirthPower_one_boundary_difference, pow_succ]
    field_simp [hne]
    <;> ring
  convert hs using 1
  · ext n
    exact heq n
  · congr 1
    ring

end
end Universality.Rule
