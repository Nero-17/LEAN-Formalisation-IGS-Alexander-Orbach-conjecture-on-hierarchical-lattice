import Universality.Percolation.FixedPointCutCriterion
import Universality.Matrix.ResponseDominance

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem reliability_pos_iff_connected {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    0 < R.reliability p ↔ R.fullGraph.Reachable R.source R.target := by
  rw [← R.conditioningProbability_connected p, R.conditioningProbability_pos_iff hp hp' .connected]
  constructor
  · rintro ⟨ω, hω⟩
    apply (R.crosses_eq_true (fun _ => true)).mp
    exact R.crosses_mono ω (fun _ => true) (fun _ _ => rfl) hω
  · intro h
    exact ⟨fun _ => true, (R.crosses_eq_true _).mpr h⟩

theorem boolean_chain_transition (f : ℕ → Bool) (n : ℕ)
    (hzero : f 0 = false) (hn : f n = true) :
    ∃ k, k < n ∧ f k = false ∧ f (k + 1) = true := by
  induction n with
  | zero => rw [hzero] at hn; contradiction
  | succ n ih =>
    cases h : f n
    · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
    · obtain ⟨k, hk, hkfalse, hktrue⟩ := ih h
      exact ⟨k, hk.trans (Nat.lt_succ_self n), hkfalse, hktrue⟩

def openingPrefix (edges n : ℕ) : Configuration edges := fun edge => decide (edge.val < n)

theorem openingPrefix_zero : openingPrefix edges 0 = fun _ => false := by
  funext edge
  simp [openingPrefix]

theorem openingPrefix_all : openingPrefix edges edges = fun _ => true := by
  funext edge
  simp [openingPrefix, edge.isLt]

theorem openingPrefix_successor (k : ℕ) (hk : k < edges) :
    openingPrefix edges (k + 1) = Function.update (openingPrefix edges k) ⟨k, hk⟩ true := by
  funext edge
  by_cases he : edge = ⟨k, hk⟩
  · subst edge
    simp [openingPrefix]
  · have hne : edge.val ≠ k := by
      intro h
      apply he
      exact Fin.ext h
    simp only [Function.update_of_ne he, openingPrefix]
    change decide (edge.val < k + 1) = decide (edge.val < k)
    have hiff : edge.val < k + 1 ↔ edge.val < k := by omega
    simp only [hiff]

theorem exists_pivotal_configuration
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    ∃ ω edge, R.pivotal ω edge = true := by
  have hzero : R.crosses (openingPrefix edges 0) = false := by
    rw [openingPrefix_zero, R.crosses_all_closed]
  have hall : R.crosses (openingPrefix edges edges) = true := by
    rw [openingPrefix_all]
    exact (R.crosses_eq_true _).mpr hconnected
  obtain ⟨k, hk, hclosed, hopen⟩ := boolean_chain_transition
    (fun n => R.crosses (openingPrefix edges n)) edges hzero hall
  refine ⟨openingPrefix edges k, ⟨k, hk⟩, ?_⟩
  have hself : Function.update (openingPrefix edges k) ⟨k, hk⟩ false = openingPrefix edges k := by
    have h := Function.update_eq_self ⟨k, hk⟩ (openingPrefix edges k)
    simpa only [openingPrefix, lt_self_iff_false, decide_false] using h
  simp only [pivotal, ← openingPrefix_successor k hk, hself, hopen, hclosed,
    Bool.not_false, Bool.and_true]

theorem reliability_derivative_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    0 < deriv R.reliability p := by
  rw [R.russo_formula]
  unfold expectation
  apply (Finset.sum_pos_iff_of_nonneg (fun ω _ =>
    mul_nonneg (bernoulliWeight_pos hp hp' ω).le (Nat.cast_nonneg _))).mpr
  obtain ⟨ω, edge, he⟩ := R.exists_pivotal_configuration hconnected
  refine ⟨ω, Finset.mem_univ _, mul_pos (bernoulliWeight_pos hp hp' ω) ?_⟩
  have hc : 0 < R.pivotalCount ω := by
    apply Finset.card_pos.mpr
    exact ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  exact_mod_cast hc

end
end Universality.FiniteNetwork
