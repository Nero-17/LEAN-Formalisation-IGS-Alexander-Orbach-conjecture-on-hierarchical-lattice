import Universality.Percolation.SingleTerminalGenerationMean
import Universality.Percolation.SubcriticalCrossingSummability
import Universality.Analysis.GeometricRecursionLimit
import Universality.Graph.IncidentDegree

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.subcritical_boundary_error_summable {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical) :
    Summable (fun n : ℕ => ((rule.generation (n + 1)).vertices : ℝ) *
      ((rule.edges : ℝ) * (rule.generation n).network.reliability p)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hmpos := lt_trans zero_lt_one hm
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  let volumeBound : ℝ := ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1) + 1
  have hvolumeBound : 0 < volumeBound := by
    exact add_pos (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)) zero_lt_one
  have hvolume : ∀ᶠ n : ℕ in atTop,
      ((rule.generation (n + 1)).vertices : ℝ) ≤ volumeBound * (rule.edges : ℝ) ^ ((n + 1) + 1) := by
    have hlimit := (rule.generation_volume_ratio_tendsto h.edges_gt_one).comp (tendsto_add_atTop_nat 1)
    filter_upwards [hlimit.eventually_le_const (lt_add_one
      (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)))] with n hn
    exact (div_le_iff₀ (pow_pos hmpos _)).mp hn
  have hq := h.subcritical_generation_crossing_weighted_summable critical p (rule.edges : ℝ)
    hc hc' hfixed hp hpc hmpos
  apply (hq.mul_left (volumeBound * (rule.edges : ℝ) ^ 3)).of_norm_bounded_eventually_nat
  filter_upwards [hvolume] with n hn
  have hqnonneg := (rule.generation n).network.reliability_nonneg hp (hpc.trans hc').le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hmpos.le hqnonneg))]
  calc
    _ ≤ (volumeBound * (rule.edges : ℝ) ^ ((n + 1) + 1)) *
        ((rule.edges : ℝ) * (rule.generation n).network.reliability p) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg hmpos.le hqnonneg)
    _ = _ := by simp only [pow_succ]; ring

/-- The actual unconditional one-terminal internal mean has a strictly
positive limit after normalization by the true terminal degree below p_c. -/
theorem Classical.subcritical_source_mean_limit {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    ∃ limit : ℝ, 0 < limit ∧ Tendsto (fun n : ℕ =>
      (rule.generation n).network.expectedInternalSourceMass p /
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n) atTop (𝓝 limit) := by
  rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
  apply positive_geometric_recursion_limit
    (fun n => (rule.generation n).network.expectedInternalSourceMass p)
    (fun n => ((rule.generation (n + 1)).vertices : ℝ) *
      ((rule.edges : ℝ) * (rule.generation n).network.reliability p))
    (rule.network.sourceIncidentEdges.card : ℝ)
  · have hd := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 1 ≤ rule.network.sourceIncidentEdges.card)
  · exact rule.network.expectedInternalSourceMass_pos hp (hpc.trans hc') (h.connected _) h.scale
  · intro n
    exact (h.generation_source_mean_bounds hp.le (hpc.trans hc').le n).1
  · intro n
    exact (h.generation_source_mean_bounds hp.le (hpc.trans hc').le n).2
  · exact h.subcritical_boundary_error_summable critical p hc hc' hfixed hp.le hpc

end
end Universality.Rule
