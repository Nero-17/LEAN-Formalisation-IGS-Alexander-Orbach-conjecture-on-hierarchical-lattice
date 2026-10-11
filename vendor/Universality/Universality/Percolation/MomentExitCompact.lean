import Universality.Percolation.MomentExitTime

namespace Universality.Rule
noncomputable section

 theorem Classical.reliability_orbit_interior_side {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hp' : p < 1) (n : ℕ) :
    0 < rule.network.reliability^[n] p ∧ rule.network.reliability^[n] p < 1 ∧
      (p < critical → rule.network.reliability^[n] p ≤ p) ∧
      (critical < p → p ≤ rule.network.reliability^[n] p) := by
  induction n with
  | zero => exact ⟨hp, hp', fun _ => le_rfl, fun _ => le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨(rule.network.reliability_pos_iff_connected ih.1 ih.2.1).mpr (h.connected _),
      rule.network.reliability_lt_one ih.1 ih.2.1, ?_, ?_⟩
    · intro hbelow
      exact (rule.network.reliability_le_parameter_below_fixed critical _ hc hc' hfixed ih.1.le
        ((ih.2.2.1 hbelow).trans_lt hbelow) h.scale).trans (ih.2.2.1 hbelow)
    · intro habove
      exact (ih.2.2.2 habove).trans (rule.network.parameter_le_reliability_above_fixed critical _ hc hc' hfixed
        (habove.trans_le (ih.2.2.2 habove)) ih.2.1.le h.scale)

/-- An arbitrary sufficiently small critical neighborhood has fixed
interior exit bounds. The last two implications keep the exits uniformly
separated from critical on the appropriate side. -/
theorem Classical.reliability_exit_compact {rule : Rule} (h : rule.Classical)
    (critical radius : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hradius : 0 < radius)
    (hradiusCritical : radius < critical) (hradiusOne : radius < 1 - critical) :
    0 < rule.network.reliability (critical - radius) ∧
    rule.network.reliability (critical + radius) < 1 ∧
    rule.network.reliability (critical - radius) ≤ critical - radius ∧
    critical + radius ≤ rule.network.reliability (critical + radius) ∧
    ∀ p, 0 < p → p < 1 → p ≠ critical → |p - critical| < radius →
      rule.network.reliability^[rule.reliabilityExitTime critical radius p] p ∈
        Set.Icc (rule.network.reliability (critical - radius)) (rule.network.reliability (critical + radius)) ∧
      (p < critical → rule.network.reliability^[rule.reliabilityExitTime critical radius p] p ≤ critical - radius) ∧
      (critical < p → critical + radius ≤ rule.network.reliability^[rule.reliabilityExitTime critical radius p] p) := by
  have hleftPos : 0 < critical - radius := sub_pos.mpr hradiusCritical
  have hleftCritical : critical - radius < critical := by linarith
  have hrightCritical : critical < critical + radius := by linarith
  have hrightOne : critical + radius < 1 := by linarith
  refine ⟨(rule.network.reliability_pos_iff_connected hleftPos (hleftCritical.trans hc')).mpr (h.connected _),
    rule.network.reliability_lt_one (hc.trans hrightCritical) hrightOne,
    rule.network.reliability_le_parameter_below_fixed critical _ hc hc' hfixed hleftPos.le hleftCritical h.scale,
    rule.network.parameter_le_reliability_above_fixed critical _ hc hc' hfixed hrightCritical hrightOne.le h.scale, ?_⟩
  intro p hp hp' hne hnear
  have hpositive := h.reliability_exit_pos critical radius p hc hc' hfixed hradiusCritical hradiusOne hp hp' hne hnear
  obtain ⟨previous, hprevious⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  have hpreviousIndex : previous < rule.reliabilityExitTime critical radius p := by omega
  have hbefore := h.reliability_exit_before critical radius p hc hc' hfixed hradiusCritical hradiusOne hp hp' hne previous hpreviousIndex
  have hbeforeBounds := abs_lt.mp hbefore
  have hpreviousOrbit := h.reliability_orbit_interior_side critical p hc hc' hfixed hp hp' previous
  have hleft := rule.network.reliability_monotoneOn
    ⟨hleftPos.le, (hleftCritical.trans hc').le⟩ ⟨hpreviousOrbit.1.le, hpreviousOrbit.2.1.le⟩
    (show critical - radius ≤ rule.network.reliability^[previous] p by linarith)
  have hright := rule.network.reliability_monotoneOn
    ⟨hpreviousOrbit.1.le, hpreviousOrbit.2.1.le⟩ ⟨(hc.trans hrightCritical).le, hrightOne.le⟩
    (show rule.network.reliability^[previous] p ≤ critical + radius by linarith)
  have hstep : rule.network.reliability (rule.network.reliability^[previous] p) =
      rule.network.reliability^[rule.reliabilityExitTime critical radius p] p := by
    rw [hprevious, Function.iterate_succ_apply']
  rw [hstep] at hleft hright
  have hafter := h.reliability_exit_spec critical radius p hc hc' hfixed hradiusCritical hradiusOne hp hp' hne
  have hside := h.reliability_orbit_interior_side critical p hc hc' hfixed hp hp' (rule.reliabilityExitTime critical radius p)
  refine ⟨⟨hleft, hright⟩, ?_, ?_⟩
  · intro hbelow
    have hbound := hside.2.2.1 hbelow
    rw [abs_of_neg (sub_neg.mpr (hbound.trans_lt hbelow))] at hafter
    linarith
  · intro habove
    have hbound := hside.2.2.2 habove
    rw [abs_of_pos (sub_pos.mpr (habove.trans_le hbound))] at hafter
    linarith

end
end Universality.Rule
