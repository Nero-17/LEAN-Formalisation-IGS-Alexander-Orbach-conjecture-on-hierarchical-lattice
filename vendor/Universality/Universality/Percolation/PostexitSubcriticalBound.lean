import Universality.Percolation.PostexitInitialComparison
import Universality.Percolation.BernoulliMonotonicity

namespace Universality.Rule
noncomputable section

theorem Classical.postexit_boundary_moment_comparison {rule : Rule} (h : rule.Classical)
    (p exitParameter : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hexit : 0 < exitParameter) (hexit' : exitParameter < 1)
    (offset : ℕ) (hparameter : rule.network.reliability^[offset] p = exitParameter)
    (scale : ℝ) (hscale : 1 ≤ scale) (order : ℕ)
    (hbase : ∀ state k, k ≤ order →
      (rule.generation offset).network.conditionalVertexMoment p state k ≤
        scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) (n : ℕ) :
    (rule.generation (offset + n)).network.expectedInternalBoundaryMoment p order ≤
      scale ^ order * (rule.generation n).network.expectedInternalBoundaryMoment exitParameter order := by
  have hcrossing : (rule.generation (offset + n)).network.reliability p =
      (rule.generation n).network.reliability exitParameter := by
    rw [rule.generation_reliability_iterate, rule.generation_reliability_iterate, ← hparameter,
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hfinePositive := ((rule.generation (offset + n)).network.reliability_pos_iff_connected hp hp').mpr
    ((h.generation (offset + n)).connected _)
  have hcoarsePositive := ((rule.generation n).network.reliability_pos_iff_connected hexit hexit').mpr
    ((h.generation n).connected _)
  have hcoarseLess := (rule.generation n).network.reliability_lt_one hexit hexit'
  rw [(rule.generation (offset + n)).network.expectedInternalBoundaryMoment_disintegrate p hfinePositive
    ((rule.generation (offset + n)).network.reliability_lt_one hp hp'),
    (rule.generation n).network.expectedInternalBoundaryMoment_disintegrate exitParameter hcoarsePositive hcoarseLess, hcrossing]
  have hb := h.postexit_moment_initial_comparison p exitParameter hp hp' hexit hexit' offset hparameter scale hscale order hbase
  have hconnected := mul_le_mul_of_nonneg_left (hb n .connected order le_rfl) hcoarsePositive.le
  have hboth := mul_le_mul_of_nonneg_left (hb n .both order le_rfl) (sub_nonneg.mpr hcoarseLess.le)
  nlinarith

/-- A fixed-subcritical post-exit birth bound uniform over the entire exit
interval. The only scale input is the finite-order initial comparison. -/
theorem Classical.postexit_subcritical_birth_bound {rule : Rule} (h : rule.Classical)
    (critical upperParameter : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hu : 0 < upperParameter)
    (huc : upperParameter < critical) (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ p exitParameter : ℝ, 0 < p → p < 1 →
      0 < exitParameter → exitParameter ≤ upperParameter → ∀ offset : ℕ,
      rule.network.reliability^[offset] p = exitParameter → ∀ scale : ℝ, 1 ≤ scale →
      (∀ state k, k ≤ order → (rule.generation offset).network.conditionalVertexMoment p state k ≤
        scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) → ∀ n : ℕ,
        rule.expectedClusterBirthPower p order (offset + n + 1) ≤
          bound * scale ^ order * (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) := by
  obtain ⟨boundaryBound, hboundaryBound, hboundary⟩ :=
    h.subcritical_boundary_moment_uniform_bound critical upperParameter hc hc' hfixed hu.le huc order horder
  have hedges : (0 : ℝ) < rule.edges := by have := h.edges_gt_one; exact_mod_cast (by omega : 0 < rule.edges)
  have hvertices : (0 : ℝ) < rule.vertices := by have := h.vertices_gt_two; exact_mod_cast (by omega : 0 < rule.vertices)
  have hdegree : (1 : ℝ) ≤ rule.network.fullGraph.degree rule.network.source := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    have := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 1 ≤ rule.network.sourceIncidentEdges.card)
  refine ⟨((rule.edges : ℝ) + 1) ^ (order - 1) *
    ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * boundaryBound), by positivity, ?_⟩
  intro p exitParameter hp hp' hexit hexitUpper offset hparameter scale hscale hbase n
  have hcoarseBound := hboundary exitParameter hexit.le hexitUpper n
  have hfineBound := (h.postexit_boundary_moment_comparison p exitParameter hp hp' hexit
    (hexitUpper.trans_lt (huc.trans hc')) offset hparameter scale hscale order hbase n).trans
      (mul_le_mul_of_nonneg_left hcoarseBound (pow_nonneg (zero_le_one.trans hscale) _))
  have hbirth := rule.network.expectedBirthClusterPower_le_boundary_moment
    (rule.generation (offset + n)).network hp.le hp'.le order horder
  change rule.expectedClusterBirthPower p order (offset + n + 1) ≤ _ at hbirth
  apply hbirth.trans
  have hdegreePower := one_le_pow₀ (n := order * n) hdegree
  have hscalePower := one_le_pow₀ (n := order) hscale
  have hbothPower : 1 ≤ scale ^ order *
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) :=
    hscalePower.trans (le_mul_of_one_le_right (zero_le_one.trans hscalePower) hdegreePower)
  have hvertexTerm := mul_le_mul_of_nonneg_left hbothPower (pow_nonneg hvertices.le order)
  have hboundaryTerm := mul_le_mul_of_nonneg_left hfineBound hedges.le
  have hinside : (rule.vertices : ℝ) ^ order + (rule.edges : ℝ) *
      (rule.generation (offset + n)).network.expectedInternalBoundaryMoment p order ≤
      ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * boundaryBound) * scale ^ order *
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) := by nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinside
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (rule.edges : ℝ) + 1) _)

end
end Universality.Rule
