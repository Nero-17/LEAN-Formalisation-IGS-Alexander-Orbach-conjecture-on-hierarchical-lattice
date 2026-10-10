import Universality.Percolation.SubcriticalBirthFirstMoment

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology ENNReal

theorem Classical.subcritical_birth_moment_eventual_lower_bound {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ᶠ n : ℕ in atTop,
      lower * (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) ≤
        rule.expectedClusterBirthPower p order (n + 1) := by
  obtain ⟨limit, hpositive, hlimit⟩ := h.subcritical_birth_first_moment_limit critical p hc hc' hfixed hp hpc
  have hp' := hpc.trans hc'
  have hradius : 0 < (rule.network.fullGraph.degree rule.network.source : ℝ) := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    have hd := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 0 < rule.network.sourceIncidentEdges.card)
  have hvertices : (0 : ℝ) < rule.vertices := by
    have := h.vertices_gt_two
    exact_mod_cast (by omega : 0 < rule.vertices)
  refine ⟨(limit / 2) ^ order / (rule.vertices : ℝ) ^ (order - 1),
    div_pos (pow_pos (half_pos hpositive) _) (pow_pos hvertices _), ?_⟩
  filter_upwards [hlimit.eventually (Ioi_mem_nhds (half_lt_self hpositive))] with n hn
  have hmean : (limit / 2) *
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n ≤
      rule.expectedClusterBirthPower p 1 (n + 1) :=
    ((lt_div_iff₀ (pow_pos hradius n)).mp hn).le
  have hpower := pow_le_pow_left₀ (mul_nonneg (half_pos hpositive).le (pow_nonneg hradius.le _)) hmean order
  have hjensen := rule.network.expectedBirthClusterPower_mean_pow_le
    (rule.generation n).network hp.le hp'.le order horder
  change rule.expectedClusterBirthPower p 1 (n + 1) ^ order ≤
    (rule.vertices : ℝ) ^ (order - 1) * rule.expectedClusterBirthPower p order (n + 1) at hjensen
  calc
    _ = ((limit / 2) *
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n) ^ order /
          (rule.vertices : ℝ) ^ (order - 1) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm n order]
      ring
    _ ≤ _ := (div_le_iff₀ (pow_pos hvertices (order - 1))).mpr
      (by simpa only [mul_comm (rule.expectedClusterBirthPower p order (n + 1))] using hpower.trans hjensen)

end
end Universality.Rule
