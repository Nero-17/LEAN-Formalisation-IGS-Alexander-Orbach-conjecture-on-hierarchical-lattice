import Universality.Percolation.SingleTerminalMomentRecursion
import Universality.Percolation.SubcriticalSourceMeanLimit
import Universality.Analysis.GeometricRecursionUpper

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.subcritical_moment_error_summable {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical)
    (order : ℕ) :
    Summable (fun n : ℕ => ((rule.generation (n + 1)).vertices : ℝ) ^ order *
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
  have hq := h.subcritical_generation_crossing_weighted_summable critical p ((rule.edges : ℝ) ^ order)
    hc hc' hfixed hp hpc (pow_pos hmpos _)
  apply (hq.mul_left (volumeBound ^ order * (rule.edges : ℝ) ^ (2 * order + 1))).of_norm_bounded_eventually_nat
  filter_upwards [hvolume] with n hn
  have hqnonneg := (rule.generation n).network.reliability_nonneg hp (hpc.trans hc').le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg hmpos.le hqnonneg))]
  calc
    _ ≤ (volumeBound * (rule.edges : ℝ) ^ ((n + 1) + 1)) ^ order *
        ((rule.edges : ℝ) * (rule.generation n).network.reliability p) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hn _)
        (mul_nonneg hmpos.le hqnonneg)
    _ = _ := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      have heq : ((n + 1) + 1) * order = order * n + 2 * order := by ring
      rw [heq, pow_add, pow_add]
      ring

theorem Classical.subcritical_source_moment_bound {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n,
      (rule.generation n).network.expectedInternalSourceMoment p order ≤
        bound * (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) := by
  have hd : (1 : ℝ) ≤ rule.network.fullGraph.degree rule.network.source := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    have hd := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 1 ≤ rule.network.sourceIncidentEdges.card)
  obtain ⟨bound, hbound, hresult⟩ := geometric_recursion_upper_bound
    (fun n => (rule.generation n).network.expectedInternalSourceMoment p order)
    (fun n => ((rule.generation (n + 1)).vertices : ℝ) ^ order *
      ((rule.edges : ℝ) * (rule.generation n).network.reliability p))
    ((rule.network.fullGraph.degree rule.network.source : ℝ) ^ order) (one_le_pow₀ hd)
    (fun n => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (Nat.cast_nonneg _) ((rule.generation n).network.reliability_nonneg hp (hpc.trans hc').le)))
    (h.generation_source_moment_le hp (hpc.trans hc').le order horder)
    (h.subcritical_moment_error_summable critical p hc hc' hfixed hp hpc order)
  refine ⟨bound, hbound, ?_⟩
  intro n
  simpa only [pow_mul] using hresult n

end
end Universality.Rule
