import Universality.Percolation.RadiusPointCounts

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem Classical.internal_radius_point_partial_sum_le_limit {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius n : ℕ) :
    (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
      (((rule.generation n).network.expectedInternalRadiusRootCount p radius -
        (rule.generation n).network.expectedInternalRadiusRootCount p (radius + 1)) /
        (rule.edges : ℝ) ^ (n + 1)) ≤ rule.limitingRootRadiusProbability p radius := by
  have hfirst := rule.radius_birth_series_summable h.edges_gt_one h.vertices_gt_two hp hp' radius
  have hsecond := rule.radius_birth_series_summable h.edges_gt_one h.vertices_gt_two hp hp' (radius + 1)
  unfold limitingRootRadiusProbability limitingRootRadiusTailProbability
  rw [← mul_sub, ← hfirst.tsum_sub hsecond]
  apply mul_le_mul_of_nonneg_left
  · rw [sub_div, h.generation_radius_normalized, h.generation_radius_normalized, ← Finset.sum_sub_distrib]
    exact (hfirst.sub hsecond).sum_le_tsum _ (fun k _ => by
      rw [← mul_sub]
      exact mul_nonneg (by positivity) (sub_nonneg.mpr
        (rule.expectedRadiusBirth_antitone hp hp' k (Nat.le_succ radius))))
  · exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast h.edges_gt_one.le))
      (sub_nonneg.mpr (by exact_mod_cast h.vertices_gt_two.le))

theorem Classical.internal_radius_point_expectation_le_limit {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius n : ℕ) :
    (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
      ((rule.generation n).network.expectedInternalRadiusPointRootCount p radius /
        (rule.edges : ℝ) ^ (n + 1)) ≤ rule.limitingRootRadiusProbability p radius := by
  rw [FiniteNetwork.expectedInternalRadiusPointRootCount_eq_difference]
  exact h.internal_radius_point_partial_sum_le_limit hp hp' radius n

end
end Universality.Rule
