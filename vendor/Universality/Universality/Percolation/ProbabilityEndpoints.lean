import Universality.Percolation.FiniteMassDimension

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem bernoulliWeight_endpoint (opened : Bool) (ω : Configuration edges) :
    bernoulliWeight (if opened then 1 else 0) ω = if ω = (fun _ => opened) then 1 else 0 := by
  by_cases heq : ω = (fun _ => opened)
  · subst ω
    cases opened <;> simp [bernoulliWeight]
  · rw [if_neg heq]
    obtain ⟨edge, he⟩ : ∃ edge, ω edge ≠ opened := by
      by_contra h
      apply heq
      funext edge
      by_contra he
      exact h ⟨edge, he⟩
    unfold bernoulliWeight
    apply Finset.prod_eq_zero (Finset.mem_univ edge)
    cases opened <;> cases hω : ω edge <;> simp_all

theorem expectation_endpoint (opened : Bool) (response : Configuration edges → ℝ) :
    expectation (if opened then 1 else 0) response = response (fun _ => opened) := by
  simp only [expectation, bernoulliWeight_endpoint]
  simp

theorem reliability_zero : R.reliability 0 = 0 := by
  have h := expectation_endpoint false R.crossingIndicator
  simp only [Bool.false_eq_true, ↓reduceIte, R.expectation_crossingIndicator] at h
  simpa only [crossingIndicator, R.crosses_all_closed, Bool.false_eq_true, ↓reduceIte] using h

theorem reliability_one (hconnected : R.fullGraph.Reachable R.source R.target) :
    R.reliability 1 = 1 := by
  have h := expectation_endpoint true R.crossingIndicator
  simp only [↓reduceIte, R.expectation_crossingIndicator] at h
  simpa only [crossingIndicator, (R.crosses_eq_true _).mpr hconnected, ↓reduceIte] using h

theorem derivative_one_zero (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) :
    deriv R.reliability 1 = 0 := by
  rw [R.russo_formula]
  have h := expectation_endpoint true (fun ω => (R.pivotalCount ω : ℝ))
  change expectation 1 _ = _ at h
  rw [h]
  have hpiv : ∀ edge, R.pivotal (fun _ => true) edge = false := by
    intro edge
    change (R.crosses (Function.update (fun _ => true) edge true) &&
      !R.crosses (onlyClosed edge)) = false
    simp only [hcut, Bool.not_true, Bool.and_false]
  simp [pivotalCount, hpiv]

theorem derivative_zero_zero (hscale : 1 < R.fullGraph.dist R.source R.target) :
    deriv R.reliability 0 = 0 := by
  rw [R.russo_formula]
  have h := expectation_endpoint false (fun ω => (R.pivotalCount ω : ℝ))
  change expectation 0 _ = _ at h
  rw [h]
  have hpiv : ∀ edge, R.pivotal (fun _ => false) edge = false := by
    intro edge
    have hnotadj : ¬ R.fullGraph.Adj R.source R.target := by
      intro hadj
      have hd := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      omega
    have hopen : R.crosses (onlyOpen edge) = false := by
      apply Bool.eq_false_iff.mpr
      intro hc
      have hr := (R.crosses_eq_true _).mp hc
      rw [R.reachable_onlyOpen_iff] at hr
      rcases hr with h | ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩
      · exact R.terminals_distinct h
      · exact hnotadj ⟨R.terminals_distinct, edge, rfl,
          Or.inl (Prod.ext hfirst.symm hsecond)⟩
      · exact hnotadj ⟨R.terminals_distinct, edge, rfl,
          Or.inr (Prod.ext hfirst hsecond.symm)⟩
    change (R.crosses (onlyOpen edge) &&
      !R.crosses (Function.update (fun _ => false) edge false)) = false
    simp only [hopen, Bool.false_and]
  simp [pivotalCount, hpiv]

theorem crosses_onlyOpen_false_of_scale (edge : Fin edges)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    R.crosses (onlyOpen edge) = false := by
  have hnotadj : ¬ R.fullGraph.Adj R.source R.target := by
    intro hadj
    have hd := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    omega
  apply Bool.eq_false_iff.mpr
  intro hc
  have hr := (R.crosses_eq_true _).mp hc
  rw [R.reachable_onlyOpen_iff] at hr
  rcases hr with h | ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩
  · exact R.terminals_distinct h
  · exact hnotadj ⟨R.terminals_distinct, edge, rfl,
      Or.inl (Prod.ext hfirst.symm hsecond)⟩
  · exact hnotadj ⟨R.terminals_distinct, edge, rfl,
      Or.inr (Prod.ext hfirst hsecond.symm)⟩

end
end Universality.FiniteNetwork
