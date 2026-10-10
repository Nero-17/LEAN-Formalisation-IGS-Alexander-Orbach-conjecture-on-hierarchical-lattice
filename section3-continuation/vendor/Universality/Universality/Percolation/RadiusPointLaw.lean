import Universality.Percolation.RadiusOrder

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ}

def uniformVertexRadiusProbability (R : FiniteNetwork vertices edges) (p : ℝ) (radius : ℕ) : ℝ :=
  (∑ configuration, bernoulliWeight p configuration *
    ∑ root : Fin vertices, if R.rootClusterRadius configuration root = radius then (1 : ℝ) else 0) / vertices

theorem uniformVertexRadiusProbability_eq_tail_difference (R : FiniteNetwork vertices edges)
    (p : ℝ) (radius : ℕ) : R.uniformVertexRadiusProbability p radius =
      R.uniformVertexRadiusTailProbability p radius - R.uniformVertexRadiusTailProbability p (radius + 1) := by
  have hpoint (count : ℕ) : (if count = radius then (1 : ℝ) else 0) =
      (if radius ≤ count then 1 else 0) - (if radius + 1 ≤ count then 1 else 0) := by
    split_ifs <;> first | omega | norm_num
  unfold uniformVertexRadiusProbability uniformVertexRadiusTailProbability
  simp_rw [hpoint, Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib, sub_div]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

def limitingRootRadiusProbability (rule : Rule) (p : ℝ) (radius : ℕ) : ℝ :=
  rule.limitingRootRadiusTailProbability p radius - rule.limitingRootRadiusTailProbability p (radius + 1)

theorem limitingRootRadiusProbability_nonneg (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius : ℕ) :
    0 ≤ rule.limitingRootRadiusProbability p radius :=
  sub_nonneg.mpr (rule.limitingRootRadiusTailProbability_antitone hedges hvertices hp hp' (Nat.le_succ radius))

theorem Classical.uniformVertexRadiusProbability_tendsto {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) (radius : ℕ) :
    Tendsto (fun n : ℕ => (rule.generation n).network.uniformVertexRadiusProbability p radius)
      atTop (𝓝 (rule.limitingRootRadiusProbability p radius)) := by
  have hlimit := (h.uniformVertexRadiusTailProbability_tendsto p hp hp' hfixed radius).sub
    (h.uniformVertexRadiusTailProbability_tendsto p hp hp' hfixed (radius + 1))
  simpa only [limitingRootRadiusProbability, FiniteNetwork.uniformVertexRadiusProbability_eq_tail_difference] using hlimit

theorem limitingRootRadiusProbability_partial_sum (rule : Rule) (p : ℝ) (radius depth : ℕ) :
    (∑ n ∈ Finset.range depth, rule.limitingRootRadiusProbability p (radius + n)) =
      rule.limitingRootRadiusTailProbability p radius - rule.limitingRootRadiusTailProbability p (radius + depth) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    rw [Finset.sum_range_succ, ih]
    unfold limitingRootRadiusProbability
    simp only [Nat.add_assoc]
    ring

theorem Classical.limitingRootRadiusProbability_hasSum_tail {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius : ℕ) :
    HasSum (fun n : ℕ => rule.limitingRootRadiusProbability p (radius + n))
      (rule.limitingRootRadiusTailProbability p radius) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => rule.limitingRootRadiusProbability_nonneg h.edges_gt_one h.vertices_gt_two hp hp' _) _).mpr
  simp only [rule.limitingRootRadiusProbability_partial_sum]
  have hzero : Tendsto (fun depth : ℕ => rule.limitingRootRadiusTailProbability p (radius + depth)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm radius] using
      (h.limitingRootRadiusTailProbability_tendsto_zero hp hp').comp (tendsto_add_atTop_nat radius)
  simpa only [sub_zero] using (tendsto_const_nhds (x := rule.limitingRootRadiusTailProbability p radius)).sub hzero

theorem Classical.limitingRootRadiusProbability_hasSum_one {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    HasSum (rule.limitingRootRadiusProbability p) 1 := by
  have hh := h.limitingRootRadiusProbability_hasSum_tail hp.le hp'.le 0
  simpa only [Nat.zero_add, h.limitingRootRadiusTailProbability_zero p hp hp' hfixed] using hh

end
end Universality.Rule
