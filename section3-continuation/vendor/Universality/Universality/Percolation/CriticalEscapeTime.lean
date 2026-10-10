import Universality.Percolation.CriticalEscapeLocal
import Universality.Analysis.FirstPassage

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open Filter FiniteNetwork
open scoped Topology

theorem Classical.subcritical_escape_exists {rule : Rule} (h : rule.Classical)
    (critical p threshold : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical)
    (hthreshold : 0 < threshold) : ∃ n, rule.network.reliability^[n] p ≤ threshold := by
  have hzero := rule.network.iterate_reliability_tendsto_zero critical p hc hc' hfixed hp.le hpc h.scale
  obtain ⟨n, hn⟩ := (hzero.eventually (gt_mem_nhds hthreshold)).exists
  exact ⟨n, hn.le⟩

/-- A uniform bounded-error escape estimate for the actual crossing map.
The stopping time is the first crossing below a fixed subcritical threshold. -/
theorem Classical.subcritical_escape_control {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius endpoint bound : ℝ, 0 < radius ∧ radius < critical ∧
      0 < endpoint ∧ endpoint ≤ critical - radius ∧ 0 ≤ bound ∧
      ∀ p, critical - radius < p → p < critical →
        rule.network.reliability^[firstPassageBelow (fun n => rule.network.reliability^[n] p) (critical - radius)] p ∈
          Set.Icc endpoint (critical - radius) ∧
        |(firstPassageBelow (fun n => rule.network.reliability^[n] p) (critical - radius) : ℝ) *
          Real.log (deriv rule.network.reliability critical) + Real.log (critical - p)| ≤ bound := by
  obtain ⟨neighborhood, lower, upper, rate, hneighborhood, hlower, hrate, hupper, hlocal⟩ :=
    h.subcritical_local_escape_bounds critical hc hc' hfixed
  have hupperPos : 0 < upper := lt_trans zero_lt_one hupper
  obtain ⟨radius, hradius, hradiusSmall⟩ := exists_between (lt_min hneighborhood (div_pos hc hupperPos))
  have hradiusNeighborhood : radius < neighborhood := hradiusSmall.trans_le (min_le_left _ _)
  have hradiusProduct : radius * upper < critical :=
    (lt_div_iff₀ hupperPos).mp (hradiusSmall.trans_le (min_le_right _ _))
  have hradiusCritical : radius < critical := by nlinarith
  refine ⟨radius, critical - upper * radius,
    |Real.log radius| + |Real.log (upper * radius)| + rate * (upper * radius) / (lower - 1),
    hradius, hradiusCritical, by nlinarith, by nlinarith, by positivity, ?_⟩
  intro p hpThreshold hpc
  have hp : 0 < p := lt_trans (sub_pos.mpr hradiusCritical) hpThreshold
  have hexists := h.subcritical_escape_exists critical p (critical - radius) hc hc' hfixed hp hpc
    (sub_pos.mpr hradiusCritical)
  let depth := firstPassageBelow (fun n => rule.network.reliability^[n] p) (critical - radius)
  have hdepth : 0 < depth := firstPassageBelow_pos _ _ hexists (by simpa using hpThreshold)
  have hbefore (n : ℕ) (hn : n < depth) :
      0 < critical - rule.network.reliability^[n] p ∧ critical - rule.network.reliability^[n] p < radius := by
    have horbit := rule.network.subcritical_reliability_orbit_bounds critical p hc hc' hfixed hp hpc h.scale (h.connected _) n
    have hminimum := firstPassageBelow_minimal _ _ hexists n hn
    exact ⟨sub_pos.mpr (horbit.2.trans_lt hpc), by linarith⟩
  have hsteps (n : ℕ) (hn : n < depth) :
      lower * (critical - rule.network.reliability^[n] p) ≤ critical - rule.network.reliability^[n + 1] p ∧
      critical - rule.network.reliability^[n + 1] p ≤ upper * (critical - rule.network.reliability^[n] p) ∧
      |Real.log (critical - rule.network.reliability^[n + 1] p) -
          Real.log (critical - rule.network.reliability^[n] p) - Real.log (deriv rule.network.reliability critical)| ≤
        rate * (critical - rule.network.reliability^[n] p) := by
    rw [Function.iterate_succ_apply']
    exact hlocal _ (sub_pos.mp (hbefore n hn).1) ((hbefore n hn).2.trans hradiusNeighborhood)
  have hexitLower : radius ≤ critical - rule.network.reliability^[depth] p := by
    have hspec := firstPassageBelow_spec _ _ hexists
    change rule.network.reliability^[depth] p ≤ critical - radius at hspec
    linarith
  have hexitUpper : critical - rule.network.reliability^[depth] p ≤ upper * radius := by
    obtain ⟨previous, hprevious⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdepth)
    have hpreviousLt : previous < depth := by omega
    have hstep := (hsteps previous hpreviousLt).2.1
    have hsmall := (hbefore previous hpreviousLt).2
    have heq : previous + 1 = depth := by omega
    rw [heq] at hstep
    exact hstep.trans (mul_le_mul_of_nonneg_left hsmall.le hupperPos.le)
  have hexitPositive := hradius.trans_le hexitLower
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  have hlogLower := Real.log_le_log hradius hexitLower
  have hlogUpper := Real.log_le_log hexitPositive hexitUpper
  have hlogBound : |Real.log (critical - rule.network.reliability^[depth] p)| ≤
      |Real.log radius| + |Real.log (upper * radius)| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log radius), abs_nonneg (Real.log (upper * radius))]
    · linarith [le_abs_self (Real.log (upper * radius)), abs_nonneg (Real.log radius)]
  have herror := finite_escape_time_error_bound (fun n => critical - rule.network.reliability^[n] p)
    (deriv rule.network.reliability critical) lower rate depth hlower hrate.le (by simpa using (sub_pos.mpr hpc).le)
    (fun n hn => (hsteps n hn).1) (fun n hn => (hsteps n hn).2.2)
  simp only [Function.iterate_zero, id_eq] at herror
  apply herror.trans
  exact add_le_add hlogBound (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexitUpper hrate.le) (sub_pos.mpr hlower).le)

theorem Classical.subcritical_escape_time_bound {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius bound : ℝ, 0 < radius ∧ radius < critical ∧ 0 ≤ bound ∧
      ∀ p, critical - radius < p → p < critical →
        |(firstPassageBelow (fun n => rule.network.reliability^[n] p) (critical - radius) : ℝ) *
          Real.log (deriv rule.network.reliability critical) + Real.log (critical - p)| ≤ bound := by
  obtain ⟨radius, endpoint, bound, hradius, hradiusCritical, _, _, hbound, hcontrol⟩ :=
    h.subcritical_escape_control critical hc hc' hfixed
  exact ⟨radius, bound, hradius, hradiusCritical, hbound, fun p hp hp' => (hcontrol p hp hp').2⟩

end
end Universality.Rule
