import Universality.Percolation.CriticalEscapeTime
import Mathlib.Analysis.Normed.Group.Bounded

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open Filter FiniteNetwork
open scoped Topology

theorem Classical.crossing_length_log_error_bound {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius bound : ℝ, 0 < radius ∧ radius < critical ∧ 0 ≤ bound ∧
      ∀ p, critical - radius < p → p < critical →
        |Real.log (rule.network.inverseCrossingLength p) -
          (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
            Real.log (deriv rule.network.reliability critical)) * Real.log (critical - p)| ≤ bound := by
  obtain ⟨radius, endpoint, escapeBound, hradius, hradiusCritical, hendpoint, hendpointThreshold,
      hescapeBound, hcontrol⟩ := h.subcritical_escape_control critical hc hc' hfixed
  have hcontinuous : ContinuousOn rule.network.inverseCrossingLength (Set.Ioo 0 critical) :=
    continuousOn_iff_continuous_restrict.mpr (h.continuous_inverseCrossingLength critical hc hc' hfixed)
  have hlogContinuous : ContinuousOn (fun p => Real.log (rule.network.inverseCrossingLength p)) (Set.Ioo 0 critical) :=
    hcontinuous.log (fun p hp => (h.crossing_length_limit critical p hc hc' hfixed hp.1 hp.2).1.ne')
  have hsubset : Set.Icc endpoint (critical - radius) ⊆ Set.Ioo 0 critical := by
    intro p hp
    exact ⟨hendpoint.trans_le hp.1, by linarith [hp.2]⟩
  obtain ⟨exitBound, hexitBound⟩ := isCompact_Icc.exists_bound_of_continuousOn (hlogContinuous.mono hsubset)
  have hexitNonneg : 0 ≤ exitBound := le_trans (norm_nonneg _)
    (hexitBound endpoint ⟨le_rfl, hendpointThreshold⟩)
  have hscale : (1 : ℝ) < rule.network.fullGraph.dist rule.network.source rule.network.target := by exact_mod_cast h.scale
  have hmultiplier := rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale
  have hlogMultiplier : 0 < Real.log (deriv rule.network.reliability critical) := Real.log_pos hmultiplier
  refine ⟨radius, exitBound +
    |Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
      Real.log (deriv rule.network.reliability critical)| * escapeBound,
    hradius, hradiusCritical, by positivity, ?_⟩
  intro p hpThreshold hpc
  have hp : 0 < p := lt_trans (sub_pos.mpr hradiusCritical) hpThreshold
  let depth := firstPassageBelow (fun n => rule.network.reliability^[n] p) (critical - radius)
  have hcontrolPoint := hcontrol p hpThreshold hpc
  have hlogExit : |Real.log (rule.network.inverseCrossingLength (rule.network.reliability^[depth] p))| ≤ exitBound := by
    simpa only [Real.norm_eq_abs] using hexitBound _ hcontrolPoint.1
  have hscaling := h.inverseCrossingLength_iterate critical p hc hc' hfixed hp hpc depth
  have hlogScaling := congrArg Real.log hscaling
  rw [Real.log_mul (pow_ne_zero _ (lt_trans zero_lt_one hscale).ne')
    (h.crossing_length_limit critical p hc hc' hfixed hp hpc).1.ne', Real.log_pow] at hlogScaling
  have hidentity : Real.log (rule.network.inverseCrossingLength p) -
      (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
        Real.log (deriv rule.network.reliability critical)) * Real.log (critical - p) =
      Real.log (rule.network.inverseCrossingLength (rule.network.reliability^[depth] p)) -
        (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
          Real.log (deriv rule.network.reliability critical)) *
          ((depth : ℝ) * Real.log (deriv rule.network.reliability critical) + Real.log (critical - p)) := by
    rw [hlogScaling]
    field_simp
    <;> ring
  rw [hidentity]
  calc
    _ ≤ |Real.log (rule.network.inverseCrossingLength (rule.network.reliability^[depth] p))| +
        |(Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
          Real.log (deriv rule.network.reliability critical)) *
          ((depth : ℝ) * Real.log (deriv rule.network.reliability critical) + Real.log (critical - p))| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add hlogExit (mul_le_mul_of_nonneg_left hcontrolPoint.2 (abs_nonneg _))

end
end Universality.Rule
