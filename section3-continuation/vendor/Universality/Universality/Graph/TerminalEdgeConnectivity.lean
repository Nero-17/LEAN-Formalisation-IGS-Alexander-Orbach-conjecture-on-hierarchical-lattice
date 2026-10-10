import Universality.Percolation.FixedPointCutCriterion

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- A cut is a set of deleted edge indices separating the two terminals. -/
def IsTerminalCut (deleted : Finset (Fin edges)) : Prop :=
  R.crosses (fun edge => decide (edge ∉ deleted)) = false

theorem exists_terminal_cut_card :
    ∃ size : ℕ, ∃ deleted : Finset (Fin edges), deleted.card = size ∧ R.IsTerminalCut deleted := by
  refine ⟨edges, Finset.univ, by simp, ?_⟩
  simpa [IsTerminalCut] using R.crosses_all_closed

/-- The minimum number of deleted edges separating the terminals. -/
def terminalEdgeConnectivity : ℕ := by
  classical
  exact Nat.find R.exists_terminal_cut_card

theorem terminalEdgeConnectivity_le (deleted : Finset (Fin edges))
    (hcut : R.IsTerminalCut deleted) : R.terminalEdgeConnectivity ≤ deleted.card := by
  classical
  exact Nat.find_min' R.exists_terminal_cut_card ⟨deleted, rfl, hcut⟩

theorem terminalEdgeConnectivity_at_least_two_iff
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    2 ≤ R.terminalEdgeConnectivity ↔ ∀ edge, R.crosses (onlyClosed edge) = true := by
  classical
  constructor
  · intro hminimum edge
    by_contra hsurvives
    have hcut : R.IsTerminalCut {edge} := by
      have hconfiguration : (fun other => decide (other ∉ ({edge} : Finset (Fin edges)))) =
          onlyClosed edge := by
        funext other
        by_cases h : other = edge <;> simp [h, onlyClosed]
      rw [IsTerminalCut, hconfiguration]
      exact Bool.eq_false_iff.mpr hsurvives
    have h := R.terminalEdgeConnectivity_le {edge} hcut
    simp only [Finset.card_singleton] at h
    omega
  · intro hsurvives
    obtain ⟨deleted, hcard, hcut⟩ := Nat.find_spec R.exists_terminal_cut_card
    change deleted.card = R.terminalEdgeConnectivity at hcard
    by_contra hminimum
    have hsmall : deleted.card = 0 ∨ deleted.card = 1 := by omega
    rcases hsmall with hempty | hsingle
    · have he : deleted = ∅ := Finset.card_eq_zero.mp hempty
      have hopen : R.crosses (fun _ => true) = true := by
        exact (R.crosses_eq_true _).mpr hconnected
      have hclosed : R.crosses (fun _ => true) = false := by
        simpa [IsTerminalCut, he] using hcut
      rw [hopen] at hclosed
      contradiction
    · obtain ⟨edge, he⟩ := Finset.card_eq_one.mp hsingle
      have hconfiguration : (fun other => decide (other ∉ deleted)) = onlyClosed edge := by
        funext other
        by_cases h : other = edge <;> simp [he, h, onlyClosed]
      have hclosed : R.crosses (onlyClosed edge) = false := by
        simpa only [IsTerminalCut, hconfiguration] using hcut
      rw [hsurvives] at hclosed
      contradiction

theorem interior_fixed_point_iff_terminalEdgeConnectivity
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    (∃ p : ℝ, 0 < p ∧ p < 1 ∧ R.reliability p = p) ↔
      2 ≤ R.terminalEdgeConnectivity := by
  rw [R.terminalEdgeConnectivity_at_least_two_iff hconnected]
  exact R.interior_fixed_point_iff_single_deletions_survive hconnected hscale

end
end Universality.FiniteNetwork
