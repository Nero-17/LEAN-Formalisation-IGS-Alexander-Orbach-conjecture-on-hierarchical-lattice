import Universality.Percolation.BernoulliMonotonicity
import Universality.Analysis.FirstPassage

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- First departure of the actual reliability orbit from a critical
neighborhood. The sign convention lets one stopping time cover both sides. -/
def reliabilityExitTime (rule : Rule) (critical radius p : ℝ) : ℕ :=
  firstPassageBelow (fun n => -|rule.network.reliability^[n] p - critical|) (-radius)

theorem Classical.reliability_exit_exists {rule : Rule} (h : rule.Classical)
    (critical radius p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hradius : radius < critical) (hradius' : radius < 1 - critical)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) :
    ∃ n, -|rule.network.reliability^[n] p - critical| ≤ -radius := by
  rcases lt_or_gt_of_ne hne with hbelow | habove
  · have ht := ((rule.network.iterate_reliability_tendsto_zero critical p hc hc' hfixed hp.le hbelow h.scale).sub_const critical).abs.neg
    have hgap : -|0 - critical| < -radius := by rw [zero_sub, abs_neg, abs_of_pos hc]; linarith
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hgap)).exists
    exact ⟨n, hn.le⟩
  · have ht := ((rule.network.iterate_reliability_tendsto_one critical p hc hc' hfixed habove hp'.le h.scale).sub_const critical).abs.neg
    have hgap : -|1 - critical| < -radius := by rw [abs_of_pos (sub_pos.mpr hc')]; linarith
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hgap)).exists
    exact ⟨n, hn.le⟩

theorem Classical.reliability_exit_before {rule : Rule} (h : rule.Classical)
    (critical radius p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hradius : radius < critical) (hradius' : radius < 1 - critical)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) (n : ℕ)
    (hn : n < rule.reliabilityExitTime critical radius p) :
    |rule.network.reliability^[n] p - critical| < radius := by
  have hh := firstPassageBelow_minimal _ _
    (h.reliability_exit_exists critical radius p hc hc' hfixed hradius hradius' hp hp' hne) n hn
  linarith

theorem Classical.reliability_exit_spec {rule : Rule} (h : rule.Classical)
    (critical radius p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hradius : radius < critical) (hradius' : radius < 1 - critical)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) :
    radius ≤ |rule.network.reliability^[rule.reliabilityExitTime critical radius p] p - critical| := by
  have hh := firstPassageBelow_spec _ _
    (h.reliability_exit_exists critical radius p hc hc' hfixed hradius hradius' hp hp' hne)
  change -|rule.network.reliability^[rule.reliabilityExitTime critical radius p] p - critical| ≤ -radius at hh
  linarith

theorem Classical.reliability_exit_pos {rule : Rule} (h : rule.Classical)
    (critical radius p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hradius : radius < critical) (hradius' : radius < 1 - critical)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) (hnear : |p - critical| < radius) :
    0 < rule.reliabilityExitTime critical radius p :=
  firstPassageBelow_pos _ _
    (h.reliability_exit_exists critical radius p hc hc' hfixed hradius hradius' hp hp' hne)
    (by simpa using neg_lt_neg hnear)

/-- Every prescribed finite orbit segment remains in the critical
neighborhood when the initial parameter is sufficiently close to critical. -/
theorem finite_reliability_orbit_near_fixed (rule : Rule) (critical radius : ℝ)
    (hfixed : rule.network.reliability critical = critical) (hradius : 0 < radius) (depth : ℕ) :
    ∃ neighborhood : ℝ, 0 < neighborhood ∧ ∀ p, |p - critical| < neighborhood →
      ∀ j ≤ depth, |rule.network.reliability^[j] p - critical| < radius := by
  have hcontinuous : Continuous rule.network.reliability :=
    continuous_iff_continuousAt.mpr (fun p => (rule.network.hasDerivAt_reliability p).continuousAt)
  have hfixedIterate (j : ℕ) : rule.network.reliability^[j] critical = critical := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfixed]
  have hlocal (j : Fin (depth + 1)) : ∀ᶠ p in 𝓝 critical,
      |rule.network.reliability^[j.val] p - critical| < radius := by
    have ht : ContinuousAt (fun p : ℝ => |rule.network.reliability^[j.val] p - critical|) critical :=
      (((hcontinuous.iterate j.val).continuousAt).sub_const critical).abs
    have hv : |rule.network.reliability^[j.val] critical - critical| < radius := by rw [hfixedIterate]; simpa using hradius
    exact ht.eventually (gt_mem_nhds hv)
  have hall : ∀ᶠ p in 𝓝 critical, ∀ j : Fin (depth + 1),
      |rule.network.reliability^[j.val] p - critical| < radius := Filter.eventually_all.mpr hlocal
  obtain ⟨neighborhood, hneighborhood, hb⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨neighborhood, hneighborhood, ?_⟩
  intro p hp j hj
  exact hb (y := p) (by simpa only [Real.dist_eq] using hp) ⟨j, by omega⟩

theorem Classical.reliability_exit_diverges {rule : Rule} (h : rule.Classical)
    (critical radius : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hradius : 0 < radius)
    (hradiusCritical : radius < critical) (hradiusOne : radius < 1 - critical) (depth : ℕ) :
    ∃ neighborhood : ℝ, 0 < neighborhood ∧ ∀ p, 0 < p → p < 1 → p ≠ critical →
      |p - critical| < neighborhood → depth < rule.reliabilityExitTime critical radius p := by
  obtain ⟨neighborhood, hneighborhood, hb⟩ := rule.finite_reliability_orbit_near_fixed critical radius hfixed hradius depth
  refine ⟨neighborhood, hneighborhood, ?_⟩
  intro p hp hp' hne hnear
  by_contra hle
  have hbefore := hb p hnear _ (Nat.le_of_not_gt hle)
  have hafter := h.reliability_exit_spec critical radius p hc hc' hfixed hradiusCritical hradiusOne hp hp' hne
  linarith

end
end Universality.Rule
