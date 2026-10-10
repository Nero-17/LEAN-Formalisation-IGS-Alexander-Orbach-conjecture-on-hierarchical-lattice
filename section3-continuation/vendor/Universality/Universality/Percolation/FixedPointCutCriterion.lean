import Universality.Percolation.InteriorFixedPoint

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem expectation_edge_open (p : ℝ) (edge : Fin edges) :
    expectation p (fun ω => if ω edge then 1 else 0) = p := by
  have h := expectation_open_independent (fun _ : Configuration edges => (1 : ℝ)) p edge
    (by intros; rfl)
  simpa only [expectation, mul_one, sum_bernoulliWeight] using h

theorem crossing_forces_cut_edge_open (edge : Fin edges)
    (hcut : R.crosses (onlyClosed edge) = false) (ω : Configuration edges)
    (hcross : R.crosses ω = true) : ω edge = true := by
  by_contra h
  have he : ω edge = false := Bool.eq_false_iff.mpr h
  have hc := R.crosses_mono ω (onlyClosed edge) (by
    intro other hopen
    by_cases ho : other = edge
    · subst other
      simp [he] at hopen
    · simp [onlyClosed, ho]) hcross
  rw [hcut] at hc
  contradiction

theorem reliability_lt_parameter_of_single_cut {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hscale : 1 < R.fullGraph.dist R.source R.target)
    (edge : Fin edges) (hcut : R.crosses (onlyClosed edge) = false) :
    R.reliability p < p := by
  rw [← R.expectation_crossingIndicator p]
  conv_rhs => rw [← expectation_edge_open p edge]
  unfold expectation
  apply Finset.sum_lt_sum
  · intro ω _
    apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_pos hp hp' ω).le
    unfold crossingIndicator
    cases hc : R.crosses ω
    · cases he : ω edge <;> norm_num [he]
    · simp [R.crossing_forces_cut_edge_open edge hcut ω hc]
  · refine ⟨onlyOpen edge, Finset.mem_univ _, ?_⟩
    have hc := R.crosses_onlyOpen_false_of_scale edge hscale
    have he : onlyOpen edge edge = true := by simp [onlyOpen]
    simp only [crossingIndicator, hc, Bool.false_eq_true, ↓reduceIte, he, mul_zero, mul_one]
    exact bernoulliWeight_pos hp hp' _

theorem interior_fixed_point_survives_single_deletion (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : R.reliability p = p)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    ∀ edge, R.crosses (onlyClosed edge) = true := by
  intro edge
  by_contra h
  have hfalse : R.crosses (onlyClosed edge) = false := Bool.eq_false_iff.mpr h
  have hlt := R.reliability_lt_parameter_of_single_cut hp hp' hscale edge hfalse
  rw [hfixed] at hlt
  exact lt_irrefl _ hlt

/-- For a connected finite rule with terminal distance at least two, a
nontrivial reliability fixed point exists exactly when no single edge is a
terminal cut. This is the finite formulation of terminal edge connectivity
at least two; no infinite-volume threshold is built into the statement. -/
theorem interior_fixed_point_iff_single_deletions_survive
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    (∃ p : ℝ, 0 < p ∧ p < 1 ∧ R.reliability p = p) ↔
      ∀ edge, R.crosses (onlyClosed edge) = true := by
  constructor
  · rintro ⟨p, hp, hp', hfixed⟩
    exact R.interior_fixed_point_survives_single_deletion p hp hp' hfixed hscale
  · exact R.exists_interior_fixed_point hconnected hscale

end
end Universality.FiniteNetwork
