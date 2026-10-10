import Universality.Percolation.SubcriticalBoundaryMomentBound

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology ENNReal

theorem Classical.subcritical_birth_moment_upper_bound {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ n,
      rule.expectedClusterBirthPower p order (n + 1) ≤ upper *
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) := by
  obtain ⟨bound, hbound, hmoment⟩ := h.subcritical_boundary_moment_bound critical p hc hc' hfixed hp hpc order horder
  have hvertices : (0 : ℝ) < rule.vertices := by
    have := h.vertices_gt_two
    exact_mod_cast (by omega : 0 < rule.vertices)
  have hedges : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hp' := hpc.trans hc'
  have hradius : 1 < (rule.network.fullGraph.degree rule.network.source : ℝ) := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    have hd := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 1 < rule.network.sourceIncidentEdges.card)
  refine ⟨((rule.edges : ℝ) + 1) ^ (order - 1) *
    ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * bound), by positivity, ?_⟩
  intro n
  have hupper := rule.network.expectedBirthClusterPower_le_boundary_moment
    (rule.generation n).network hp hp'.le order horder
  change rule.expectedClusterBirthPower p order (n + 1) ≤ _ at hupper
  apply hupper.trans
  have hpower := one_le_pow₀ (n := order * n) hradius.le
  have hmoment' := mul_le_mul_of_nonneg_left (hmoment n) hedges.le
  have hvertexPower := mul_le_mul_of_nonneg_left hpower
    (pow_nonneg hvertices.le order)
  have hinside : (rule.vertices : ℝ) ^ order +
      (rule.edges : ℝ) * (rule.generation n).network.expectedInternalBoundaryMoment p order ≤
      ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * bound) *
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) := by
    nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinside
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (rule.edges : ℝ) + 1) _)

/-- Subcritical finiteness for the actual limiting uniform-root size law. -/
theorem Classical.subcritical_root_moment_ne_top {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical)
    (order : ℕ)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) <
      (rule.edges : ℝ)) : rule.limitingRootSizeMoment p order ≠ ⊤ := by
  have hp' := hpc.trans hc'
  apply (rule.limitingRootSizeMoment_finite_iff_birth_summable
    h.edges_gt_one h.vertices_gt_two hp hp'.le order).mpr
  obtain ⟨upper, hupper, hupperBound⟩ := h.subcritical_birth_moment_upper_bound critical p hc hc' hfixed hp hpc (order + 1) (by omega)
  have hm : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hratioNonneg : 0 ≤
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) /
        (rule.edges : ℝ) := by positivity
  have hratio :
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) /
        (rule.edges : ℝ) < 1 := (div_lt_one hm).mpr hthreshold
  have hgeom := (summable_geometric_of_lt_one hratioNonneg hratio).mul_left
    (upper / (rule.edges : ℝ) ^ 2)
  apply (summable_nat_add_iff 1).mp
  apply hgeom.of_nonneg_of_le
  · intro n
    exact mul_nonneg (by positivity) (rule.expectedClusterBirthPower_nonneg hp hp'.le _ _)
  · intro n
    calc
      (1 / (rule.edges : ℝ)) ^ ((n + 1) + 1) * rule.expectedClusterBirthPower p (order + 1) (n + 1) ≤
          (1 / (rule.edges : ℝ)) ^ ((n + 1) + 1) *
            (upper * (rule.network.fullGraph.degree rule.network.source : ℝ) ^
              ((order + 1) * n)) := mul_le_mul_of_nonneg_left (hupperBound n) (by positivity)
      _ = _ := by
        rw [pow_mul, div_pow]
        simp only [pow_succ, one_div, inv_pow]
        field_simp [hm.ne']
        <;> ring_nf
        <;> simp [inv_pow, mul_assoc, hm.ne']

end
end Universality.Rule
