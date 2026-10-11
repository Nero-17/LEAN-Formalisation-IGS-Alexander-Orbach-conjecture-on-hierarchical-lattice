import Universality.Percolation.RadiusTailZero

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem clusterRadiusRootCount_antitone (R : FiniteNetwork vertices edges)
    (cluster : Finset (Fin vertices)) : Antitone (R.clusterRadiusRootCount cluster) := by
  intro a b hab
  apply Finset.card_le_card
  intro root hroot
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hroot).1, hab.trans (Finset.mem_filter.mp hroot).2⟩

theorem expectedInternalRadiusRootCount_antitone (R : FiniteNetwork vertices edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) : Antitone (R.expectedInternalRadiusRootCount p) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro configuration _
  apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' configuration)
  apply Nat.cast_le.mpr
  apply Finset.sum_le_sum
  intro cluster _
  exact R.clusterRadiusRootCount_antitone cluster hab

theorem expectedBirthRadiusRootCount_antitone (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Antitone (R.expectedBirthRadiusRootCount S p) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro configuration _
  apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' configuration)
  apply Nat.cast_le.mpr
  apply Finset.sum_le_sum
  intro cluster _
  exact (R.substitute S).clusterRadiusRootCount_antitone cluster hab

theorem uniformVertexRadiusTailProbability_zero (R : FiniteNetwork vertices edges) (p : ℝ) :
    R.uniformVertexRadiusTailProbability p 0 = 1 := by
  have hvertices : (vertices : ℝ) ≠ 0 := by
    have := R.two_le_vertices
    exact_mod_cast (by omega : vertices ≠ 0)
  simp only [uniformVertexRadiusTailProbability, Nat.zero_le, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.sum_mul, sum_bernoulliWeight, one_mul]
  exact div_self hvertices

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork Filter
open scoped Topology

theorem expectedRadiusBirth_antitone (rule : Rule) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) : Antitone (fun radius => rule.expectedRadiusBirth p radius n) := by
  cases n with
  | zero => exact rule.network.expectedInternalRadiusRootCount_antitone hp hp'
  | succ n => exact rule.network.expectedBirthRadiusRootCount_antitone _ hp hp'

theorem limitingRootRadiusTailProbability_nonneg (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius : ℕ) :
    0 ≤ rule.limitingRootRadiusTailProbability p radius := by
  apply mul_nonneg
  · apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hedges.le)
    · exact sub_nonneg.mpr (by exact_mod_cast hvertices.le)
  · exact tsum_nonneg (fun n => mul_nonneg (by positivity) (rule.expectedRadiusBirth_bounds hp hp' radius n).1)

theorem limitingRootRadiusTailProbability_antitone (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) : Antitone (rule.limitingRootRadiusTailProbability p) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left
  · exact (rule.radius_birth_series_summable hedges hvertices hp hp' b).tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (rule.expectedRadiusBirth_antitone hp hp' n hab) (by positivity))
      (rule.radius_birth_series_summable hedges hvertices hp hp' a)
  · apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hedges.le)
    · exact sub_nonneg.mpr (by exact_mod_cast hvertices.le)

theorem Classical.internal_radius_partial_sum_le_limit {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius n : ℕ) :
    (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
      ((rule.generation n).network.expectedInternalRadiusRootCount p radius / (rule.edges : ℝ) ^ (n + 1)) ≤
      rule.limitingRootRadiusTailProbability p radius := by
  unfold limitingRootRadiusTailProbability
  apply mul_le_mul_of_nonneg_left
  · rw [h.generation_radius_normalized]
    exact (rule.radius_birth_series_summable h.edges_gt_one h.vertices_gt_two hp hp' radius).sum_le_tsum _
      (fun n _ => mul_nonneg (by positivity) (rule.expectedRadiusBirth_bounds hp hp' radius n).1)
  · apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast h.edges_gt_one.le)
    · exact sub_nonneg.mpr (by exact_mod_cast h.vertices_gt_two.le)

theorem Classical.limitingRootRadiusTailProbability_zero {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    rule.limitingRootRadiusTailProbability p 0 = 1 := by
  have hlimit := h.uniformVertexRadiusTailProbability_tendsto p hp hp' hfixed 0
  simp only [FiniteNetwork.uniformVertexRadiusTailProbability_zero] at hlimit
  exact tendsto_nhds_unique hlimit tendsto_const_nhds

end
end Universality.Rule
