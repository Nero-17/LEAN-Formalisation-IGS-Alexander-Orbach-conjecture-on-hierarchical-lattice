import Universality.Percolation.CrossingLengthLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open FiniteNetwork

theorem Classical.continuous_inverseCrossingLength {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Continuous (fun p : Set.Ioo (0 : ℝ) critical => rule.network.inverseCrossingLength p.val) := by
  have hscale : (1 : ℝ) < rule.network.fullGraph.dist rule.network.source rule.network.target := by exact_mod_cast h.scale
  have hdiscount : 0 ≤ 1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) :=
    one_div_nonneg.mpr (lt_trans zero_lt_one hscale).le
  have hdiscount' : 1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) < 1 :=
    (div_lt_one (lt_trans zero_lt_one hscale)).mpr hscale
  have hmap : Continuous rule.network.reliability :=
    continuous_iff_continuousAt.mpr (fun p => (rule.network.hasDerivAt_reliability p).continuousAt)
  have hlog (n : ℕ) : Continuous (fun p : Set.Ioo (0 : ℝ) critical => Real.log (rule.network.reliability^[n] p.val)) :=
    ((hmap.iterate n).comp continuous_subtype_val).log (fun p =>
      (rule.network.subcritical_reliability_orbit_bounds critical p.val hc hc' hfixed p.property.1 p.property.2
        h.scale (h.connected _) n).1.ne')
  unfold inverseCrossingLength normalizedLogLimit
  apply Continuous.neg
  apply Continuous.add
  · exact hlog 0
  apply continuous_tsum (u := fun n : ℕ =>
    (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) ^ (n + 1) *
      (|Real.log ((1 - critical) ^ rule.edges)| + |Real.log ((2 : ℝ) ^ rule.edges)|))
  · intro n
    exact continuous_const.mul ((hlog (n + 1)).sub (continuous_const.mul (hlog n)))
  · exact ((summable_geometric_of_lt_one hdiscount hdiscount').comp_injective
      (fun a b (heq : a + 1 = b + 1) => Nat.add_right_cancel heq)).mul_right _
  · intro n p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hdiscount _)]
    exact mul_le_mul_of_nonneg_left
      (h.subcritical_log_correction_bound critical p.val hc hc' hfixed p.property.1 p.property.2 n)
      (pow_nonneg hdiscount _)

theorem Classical.inverseCrossingLength_scaling {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    rule.network.inverseCrossingLength (rule.network.reliability p) =
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) *
        rule.network.inverseCrossingLength p := by
  have hscale : (1 : ℝ) < rule.network.fullGraph.dist rule.network.source rule.network.target := by exact_mod_cast h.scale
  have hshift := normalizedLogLimit_shift (fun n => rule.network.reliability^[n] p) _ _ hscale
    (h.subcritical_log_correction_bound critical p hc hc' hfixed hp hpc) 1
  simp only [pow_one, Function.iterate_succ_apply] at hshift
  unfold inverseCrossingLength
  rw [hshift]
  ring

theorem Classical.inverseCrossingLength_iterate {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) (n : ℕ) :
    rule.network.inverseCrossingLength (rule.network.reliability^[n] p) =
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ n *
        rule.network.inverseCrossingLength p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbounds := rule.network.subcritical_reliability_orbit_bounds critical p hc hc' hfixed hp hpc h.scale (h.connected _) n
    rw [Function.iterate_succ_apply', h.inverseCrossingLength_scaling critical _ hc hc' hfixed hbounds.1
      (hbounds.2.trans_lt hpc), ih, pow_succ]
    ring

end
end Universality.Rule
