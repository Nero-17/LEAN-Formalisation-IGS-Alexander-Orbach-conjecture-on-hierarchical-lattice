import Universality.Percolation.BoundaryDensityComparison
import Universality.Percolation.PostexitFirstMomentLower
import Universality.Percolation.PostexitInitialComparison

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0

theorem Classical.postexit_escaping_mass_lower {rule : Rule} (h : rule.Classical)
    (p exitParameter : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hexit : 0 < exitParameter) (hexit' : exitParameter < 1)
    (offset : ℕ) (hparameter : rule.network.reliability^[offset] p = exitParameter)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hbase : ∀ state, scale * (rule.network.conditionalVertexMass exitParameter state + rule.vertices) ≤
      (rule.generation offset).network.conditionalVertexMass p state) :
    scale / (rule.edges : ℝ) ^ offset * rule.escapingRootMass exitParameter ≤ rule.escapingRootMass p := by
  apply rule.escapingRootMass_ge_of_shifted_boundary_bound h.edges_gt_one h.vertices_gt_two
    p exitParameter scale hp.le hp'.le hexit.le hexit'.le offset
  intro n
  have hcrossing : (rule.generation (offset + n)).network.reliability p =
      (rule.generation n).network.reliability exitParameter := by
    rw [rule.generation_reliability_iterate, rule.generation_reliability_iterate, ← hparameter,
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hq := ((rule.generation n).network.reliability_pos_iff_connected hexit hexit').mpr ((h.generation n).connected _)
  have hq' := (rule.generation n).network.reliability_lt_one hexit hexit'
  have hmass (state : LiveState) : scale * (rule.generation n).network.conditionalVertexMass exitParameter state ≤
      (rule.generation (offset + n)).network.conditionalVertexMass p state := by
    have hh := h.postexit_vertex_mass_lower_comparison p exitParameter hp hp' hexit hexit' offset hparameter scale hscale hbase n state
    nlinarith [mul_nonneg hscale (Nat.cast_nonneg rule.vertices)]
  rw [(rule.generation n).network.expectedInternalBoundaryMass_disintegrate exitParameter hq hq',
    (rule.generation (offset + n)).network.expectedInternalBoundaryMass_disintegrate p
      (by rwa [hcrossing]) (by rwa [hcrossing]), hcrossing]
  have hfirst := mul_le_mul_of_nonneg_left (hmass .connected) hq.le
  have hsecond := mul_le_mul_of_nonneg_left (hmass .both) (sub_nonneg.mpr hq'.le)
  nlinarith

theorem Classical.postexit_escaping_mass_upper {rule : Rule} (h : rule.Classical)
    (p exitParameter : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hexit : 0 < exitParameter) (hexit' : exitParameter < 1)
    (offset : ℕ) (hparameter : rule.network.reliability^[offset] p = exitParameter)
    (scale : ℝ) (hscale : 1 ≤ scale)
    (hbase : ∀ state k, k ≤ 1 → (rule.generation offset).network.conditionalVertexMoment p state k ≤
      scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) :
    rule.escapingRootMass p ≤ scale / (rule.edges : ℝ) ^ offset * rule.escapingRootMass exitParameter := by
  apply rule.escapingRootMass_le_of_shifted_boundary_bound h.edges_gt_one h.vertices_gt_two
    p exitParameter scale hp.le hp'.le hexit.le hexit'.le offset
  intro n
  have hcrossing : (rule.generation (offset + n)).network.reliability p =
      (rule.generation n).network.reliability exitParameter := by
    rw [rule.generation_reliability_iterate, rule.generation_reliability_iterate, ← hparameter,
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hq := ((rule.generation n).network.reliability_pos_iff_connected hexit hexit').mpr ((h.generation n).connected _)
  have hq' := (rule.generation n).network.reliability_lt_one hexit hexit'
  have hmass (state : LiveState) : (rule.generation (offset + n)).network.conditionalVertexMass p state ≤
      scale * (rule.generation n).network.conditionalVertexMass exitParameter state := by
    have hh := h.postexit_moment_initial_comparison p exitParameter hp hp' hexit hexit' offset hparameter
      scale hscale 1 hbase n state 1 le_rfl
    simpa only [conditionalVertexMoment_one, pow_one] using hh
  rw [(rule.generation n).network.expectedInternalBoundaryMass_disintegrate exitParameter hq hq',
    (rule.generation (offset + n)).network.expectedInternalBoundaryMass_disintegrate p
      (by rwa [hcrossing]) (by rwa [hcrossing]), hcrossing]
  have hfirst := mul_le_mul_of_nonneg_left (hmass .connected) hq.le
  have hsecond := mul_le_mul_of_nonneg_left (hmass .both) (sub_nonneg.mpr hq'.le)
  nlinarith

end
end Universality.Rule
