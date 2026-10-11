import Universality.Percolation.RadiusBirthLower
import Universality.Percolation.RadiusOrder
import Universality.Graph.GeodesicEdgeLevels
import Universality.Percolation.VertexMassGrowth

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

theorem Classical.radius_tail_geometric_lower {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ n,
      lower * (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        (rule.edges : ℝ)) ^ n ≤
      rule.limitingRootRadiusTailProbability p
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ n) := by
  obtain ⟨edge, hs, ht, hs', ht'⟩ := h.second_generation_internal_edge
  obtain ⟨constant, upper, hconstant, hupper, hmass⟩ := h.internal_vertex_mass_bounds p hp hp' hfixed
  have hweight : 0 < bernoulliWeight p (onlyOpen edge) := bernoulliWeight_pos hp hp' _
  have hm : (0 : ℝ) < rule.edges := by exact_mod_cast (by have := h.edges_gt_one; omega : 0 < rule.edges)
  have hscale : 0 < ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) :=
    div_pos (sub_pos.mpr (by exact_mod_cast h.edges_gt_one))
      (sub_pos.mpr (by exact_mod_cast h.vertices_gt_two))
  refine ⟨(((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
    (bernoulliWeight p (onlyOpen edge) * constant / (rule.edges : ℝ) ^ 3), by positivity, ?_⟩
  intro n
  have hlength : 2 * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n ≤
      (rule.generation n).network.fullGraph.dist (rule.generation n).network.source (rule.generation n).network.target := by
    rw [rule.generation_terminal_distance (h.connected _) n, pow_succ']
    exact Nat.mul_le_mul_right _ h.scale
  have hbirth := (rule.generation 1).network.expectedBirthRadiusRootCount_ge_onlyOpen_mass
    (rule.generation n).network (h.generation 1).connected (h.generation n).connected hp.le hp'.le
    (by rwa [rule.generation_fixed_point p hfixed]) (by rwa [rule.generation_fixed_point p hfixed])
    edge hs ht hs' ht' _ hlength
  rw [rule.generation_fixed_point p hfixed] at hbirth
  have hmean := mul_le_mul_of_nonneg_left (hmass n .connected).1 hweight.le
  have hrec := (rule.generation 1).network.expectedInternalRadiusRootCount_substitute
    (rule.generation n).network (h.generation n).connected p
      (rule.network.fullGraph.dist rule.network.source rule.network.target ^ n)
  have hnonnegative : 0 ≤ (rule.generation n).network.expectedInternalRadiusRootCount p
      (rule.network.fullGraph.dist rule.network.source rule.network.target ^ n) := by
    exact Finset.sum_nonneg (fun configuration _ => mul_nonneg
      (bernoulliWeight_nonneg hp.le hp'.le configuration) (Nat.cast_nonneg _))
  have hmul : 0 ≤ ((rule.generation 1).edges : ℝ) *
      (rule.generation n).network.expectedInternalRadiusRootCount p
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ n) :=
    mul_nonneg (Nat.cast_nonneg _) hnonnegative
  have hfinite : bernoulliWeight p (onlyOpen edge) *
      (constant * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ≤
      (rule.generation (1 + n + 1)).network.expectedInternalRadiusRootCount p
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ n) := by
    rw [← (rule.generationBlockDecomposition 1 n).expectedInternalRadiusRootCount (h.generation (1 + n + 1)).connected]
    linarith
  have hpartial := h.internal_radius_partial_sum_le_limit hp.le hp'.le
    (rule.network.fullGraph.dist rule.network.source rule.network.target ^ n) (1 + n + 1)
  have hbound := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hfinite (pow_nonneg hm.le (1 + n + 1 + 1))) hscale.le
  apply le_trans _ hpartial
  convert hbound using 1
  rw [show 1 + n + 1 + 1 = n + 3 by omega, pow_add, div_pow]
  field_simp
  <;> ring

end
end Universality.Rule
