import Universality.Percolation.NearCriticalTailBounds
import Universality.Percolation.MomentExitWideCompact

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0

/-- The actual first exit can be chosen in every sufficiently small
critical neighborhood, with a uniform whole-tail estimate on the supercritical side. -/
theorem Classical.actual_supercritical_exit_birth_tail {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order) :
    ∃ neighborhood : ℝ, 0 < neighborhood ∧ neighborhood < critical ∧ neighborhood < 1 - critical ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ neighborhood → ∃ constant : ℝ, 0 < constant ∧
      ∀ p, 0 < p → p < 1 → critical < p → |p - critical| < radius →
        Summable (fun j : ℕ => (1 / (rule.edges : ℝ)) ^ j *
          rule.expectedClusterBirthPower p order (rule.reliabilityExitTime critical radius p + j + 1)) ∧
        (∑' j : ℕ, (1 / (rule.edges : ℝ)) ^ j *
          rule.expectedClusterBirthPower p order (rule.reliabilityExitTime critical radius p + j + 1)) ≤
          constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^
            (order * rule.reliabilityExitTime critical radius p) := by
  obtain ⟨hlower, hupper, hinterval⟩ := h.reliability_wide_compact critical hc hc'
  obtain ⟨preRadius, hpreRadius, hb⟩ := h.nearcritical_supercritical_birth_tail critical
    (rule.network.reliability (critical / 2)) (rule.network.reliability ((1 + critical) / 2))
    hc hc' hfixed hlower hinterval hupper order horder
  let neighborhood : ℝ := min preRadius (min (critical / 2) ((1 - critical) / 2))
  have hneighborhood : 0 < neighborhood := lt_min hpreRadius (lt_min (by linarith) (by linarith))
  have hncritical : neighborhood ≤ critical / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hnone : neighborhood ≤ (1 - critical) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨neighborhood, hneighborhood, by linarith, by linarith, ?_⟩
  intro radius hradius hradiusSmall
  have hradiusCritical : radius ≤ critical / 2 := hradiusSmall.trans hncritical
  have hradiusOne : radius ≤ (1 - critical) / 2 := hradiusSmall.trans hnone
  have hradiusPre : radius ≤ preRadius := hradiusSmall.trans (min_le_left _ _)
  obtain ⟨constant, hconstant, ht⟩ := hb (critical + radius) (by linarith) (by linarith)
  refine ⟨constant, hconstant, ?_⟩
  intro p hp hp' hside hnear
  have hne : p ≠ critical := ne_of_gt hside
  have hpositive := h.reliability_exit_pos critical radius p hc hc' hfixed
    (by linarith) (by linarith) hp hp' hne hnear
  obtain ⟨previous, hprevious⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  have hpreorbit (j : ℕ) (hj : j ≤ previous) : |rule.network.reliability^[j] p - critical| < preRadius :=
    (h.reliability_exit_before critical radius p hc hc' hfixed (by linarith) (by linarith)
      hp hp' hne j (by omega)).trans_le hradiusPre
  have hwide := h.reliability_exit_wide_compact critical radius p hc hc' hfixed hradius
    hradiusCritical hradiusOne hp hp' hne hnear
  have hcompact := (h.reliability_exit_compact critical radius hc hc' hfixed hradius
    (by linarith) (by linarith)).2.2.2.2 p hp hp' hne hnear
  have hh := ht p hp hp' previous hpreorbit
    (rule.network.reliability^[rule.reliabilityExitTime critical radius p] p)
    (by rw [hprevious]) hwide.1 hwide.2 (hcompact.2.2 hside)
  rw [hprevious]
  exact hh

/-- The actual first exit can be chosen in every sufficiently small
critical neighborhood, with a uniform whole-tail estimate on the subcritical side. -/
theorem Classical.actual_subcritical_exit_birth_tail {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ order < rule.edges) :
    ∃ neighborhood : ℝ, 0 < neighborhood ∧ neighborhood < critical ∧ neighborhood < 1 - critical ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ neighborhood → ∃ constant : ℝ, 0 < constant ∧
      ∀ p, 0 < p → p < 1 → p < critical → |p - critical| < radius →
        Summable (fun j : ℕ => (1 / (rule.edges : ℝ)) ^ j *
          rule.expectedClusterBirthPower p order (rule.reliabilityExitTime critical radius p + j + 1)) ∧
        (∑' j : ℕ, (1 / (rule.edges : ℝ)) ^ j *
          rule.expectedClusterBirthPower p order (rule.reliabilityExitTime critical radius p + j + 1)) ≤
          constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^
            (order * rule.reliabilityExitTime critical radius p) := by
  obtain ⟨hlower, hupper, hinterval⟩ := h.reliability_wide_compact critical hc hc'
  obtain ⟨preRadius, hpreRadius, hb⟩ := h.nearcritical_subcritical_birth_tail critical
    (rule.network.reliability (critical / 2)) (rule.network.reliability ((1 + critical) / 2))
    hc hc' hfixed hlower hinterval hupper order horder hthreshold
  let neighborhood : ℝ := min preRadius (min (critical / 2) ((1 - critical) / 2))
  have hneighborhood : 0 < neighborhood := lt_min hpreRadius (lt_min (by linarith) (by linarith))
  have hncritical : neighborhood ≤ critical / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hnone : neighborhood ≤ (1 - critical) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨neighborhood, hneighborhood, by linarith, by linarith, ?_⟩
  intro radius hradius hradiusSmall
  have hradiusCritical : radius ≤ critical / 2 := hradiusSmall.trans hncritical
  have hradiusOne : radius ≤ (1 - critical) / 2 := hradiusSmall.trans hnone
  have hradiusPre : radius ≤ preRadius := hradiusSmall.trans (min_le_left _ _)
  obtain ⟨constant, hconstant, ht⟩ := hb (critical - radius) (by linarith) (by linarith)
  refine ⟨constant, hconstant, ?_⟩
  intro p hp hp' hside hnear
  have hne : p ≠ critical := ne_of_lt hside
  have hpositive := h.reliability_exit_pos critical radius p hc hc' hfixed
    (by linarith) (by linarith) hp hp' hne hnear
  obtain ⟨previous, hprevious⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  have hpreorbit (j : ℕ) (hj : j ≤ previous) : |rule.network.reliability^[j] p - critical| < preRadius :=
    (h.reliability_exit_before critical radius p hc hc' hfixed (by linarith) (by linarith)
      hp hp' hne j (by omega)).trans_le hradiusPre
  have hwide := h.reliability_exit_wide_compact critical radius p hc hc' hfixed hradius
    hradiusCritical hradiusOne hp hp' hne hnear
  have hcompact := (h.reliability_exit_compact critical radius hc hc' hfixed hradius
    (by linarith) (by linarith)).2.2.2.2 p hp hp' hne hnear
  have hh := ht p hp hp' previous hpreorbit
    (rule.network.reliability^[rule.reliabilityExitTime critical radius p] p)
    (by rw [hprevious]) hwide.1 hwide.2 (hcompact.2.1 hside)
  rw [hprevious]
  exact hh

end
end Universality.Rule
