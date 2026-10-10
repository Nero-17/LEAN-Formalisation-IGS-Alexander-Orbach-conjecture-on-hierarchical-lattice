import Universality.Percolation.RootEdgeResponse

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem expectation_sub (p : ℝ) (first second : Configuration edges → ℝ) :
    expectation p (fun ω => first ω - second ω) = expectation p first - expectation p second := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_open_supported (p : ℝ) (edge : Fin edges)
    (response : Configuration edges → ℝ)
    (hsupport : ∀ ω, ω edge = false → response ω = 0) :
    expectation p response = p * expectation p (fun ω => response (Function.update ω edge true)) := by
  have hfunction : response = fun ω => if ω edge then response (Function.update ω edge true) else 0 := by
    funext ω
    cases he : ω edge
    · simp [he, hsupport ω he]
    · have hu := Function.update_eq_self edge ω
      rw [he] at hu
      simp only [he, ↓reduceIte, hu]
  conv_lhs => rw [hfunction]
  apply expectation_open_independent
  intro ω opened
  rw [Function.update_idem]

theorem expectation_closed_supported (p : ℝ) (edge : Fin edges)
    (response : Configuration edges → ℝ)
    (hsupport : ∀ ω, ω edge = true → response ω = 0) :
    expectation p response = (1 - p) * expectation p (fun ω => response (Function.update ω edge false)) := by
  have hfunction : response = fun ω => if ω edge then 0 else response (Function.update ω edge false) := by
    funext ω
    cases he : ω edge
    · have hu := Function.update_eq_self edge ω
      rw [he] at hu
      simp only [he, Bool.false_eq_true, ↓reduceIte, hu]
    · simp [he, hsupport ω he]
  conv_lhs => rw [hfunction]
  apply expectation_closed_independent
  intro ω opened
  rw [Function.update_idem]

theorem childState_no_connected_of_closed (σ : LiveState) (ω : Configuration edges)
    (edge : Fin edges) (hclosed : ω edge = false) :
    R.childState σ ω edge ≠ some .connected := by
  simp only [childState, hclosed]
  cases R.active σ ω (R.endpoint edge).1 <;>
    cases R.active σ ω (R.endpoint edge).2 <;> simp

theorem childState_no_closed_of_open (σ : LiveState) (ω : Configuration edges)
    (edge : Fin edges) (hopen : ω edge = true) :
    R.childState σ ω edge ≠ some .both ∧ R.childState σ ω edge ≠ some .single := by
  have heq := R.active_endpoints_eq_of_open σ ω edge hopen
  simp only [childState, ← heq, hopen]
  cases R.active σ ω (R.endpoint edge).1 <;> simp

theorem expected_connected_edge_score (p : ℝ) (edge : Fin edges) :
    (1 - p) * expectation p (fun ω => R.connectedOpenEdgeIndicator ω edge) -
      p * expectation p (fun ω => R.connectedClosedEdgeIndicator ω edge) =
        p * (1 - p) * expectation p (fun ω => if R.pivotal ω edge then 1 else 0) := by
  rw [expectation_open_supported p edge (fun ω => R.connectedOpenEdgeIndicator ω edge) (by
    intro ω he
    simp [connectedOpenEdgeIndicator, R.childState_no_connected_of_closed .connected ω edge he])]
  rw [expectation_closed_supported p edge (fun ω => R.connectedClosedEdgeIndicator ω edge) (by
    intro ω he
    have h := R.childState_no_closed_of_open .connected ω edge he
    simp [connectedClosedEdgeIndicator, h.1, h.2])]
  have hpair : (fun ω => R.connectedOpenEdgeIndicator (Function.update ω edge true) edge -
      R.connectedClosedEdgeIndicator (Function.update ω edge false) edge) =
        fun ω => if R.pivotal ω edge then (1 : ℝ) else 0 := by
    funext ω
    exact (R.root_edge_pairing ω edge).1
  rw [← hpair, expectation_sub]
  ring

theorem expected_disconnected_edge_score (p : ℝ) (edge : Fin edges) :
    (1 - p) * expectation p (fun ω => R.disconnectedOpenEdgeIndicator ω edge) -
      p * expectation p (fun ω => R.disconnectedClosedEdgeIndicator ω edge) =
        -(p * (1 - p) * expectation p (fun ω => if R.pivotal ω edge then 1 else 0)) := by
  rw [expectation_open_supported p edge (fun ω => R.disconnectedOpenEdgeIndicator ω edge) (by
    intro ω he
    simp [disconnectedOpenEdgeIndicator, R.childState_no_connected_of_closed .single ω edge he])]
  rw [expectation_closed_supported p edge (fun ω => R.disconnectedClosedEdgeIndicator ω edge) (by
    intro ω he
    have h := R.childState_no_closed_of_open .single ω edge he
    simp [disconnectedClosedEdgeIndicator, h.1, h.2])]
  have hpair : (fun ω => R.disconnectedOpenEdgeIndicator (Function.update ω edge true) edge -
      R.disconnectedClosedEdgeIndicator (Function.update ω edge false) edge) =
        fun ω => -(if R.pivotal ω edge then (1 : ℝ) else 0) := by
    funext ω
    exact (R.root_edge_pairing ω edge).2
  have hexpect := congrArg (expectation p) hpair
  rw [expectation_sub] at hexpect
  simp only [expectation, mul_neg, Finset.sum_neg_distrib] at hexpect
  change _ = -(p * (1 - p) * expectation p (fun ω => if R.pivotal ω edge then 1 else 0))
  change expectation p _ - expectation p _ = - expectation p _ at hexpect
  nlinarith [congrArg (fun x : ℝ => p * (1 - p) * x) hexpect]

def countingMoment (p : ℝ) (σ τ : LiveState) : ℝ :=
  ∑ ω : Configuration edges,
    if R.conditioning σ ω then bernoulliWeight p ω * R.liveCount σ τ ω else 0

theorem countingMoment_as_edge_sum (p : ℝ) (σ τ : LiveState) :
    R.countingMoment p σ τ = ∑ edge : Fin edges,
      expectation p (fun ω => if R.conditioning σ ω then
        (if R.childState σ ω edge = some τ then 1 else 0) else 0) := by
  unfold countingMoment expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [liveCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  cases hc : R.conditioning σ ω <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, Finset.mul_sum, mul_ite,
      mul_one, mul_zero, Finset.sum_const_zero]

theorem connected_open_edge_sum (p : ℝ) :
    R.countingMoment p .connected .connected =
      ∑ edge, expectation p (fun ω => R.connectedOpenEdgeIndicator ω edge) := by
  rw [countingMoment_as_edge_sum]
  rfl

theorem disconnected_open_edge_sum (p : ℝ) :
    R.countingMoment p .single .connected =
      ∑ edge, expectation p (fun ω => R.disconnectedOpenEdgeIndicator ω edge) := by
  rw [countingMoment_as_edge_sum]
  apply Finset.sum_congr rfl
  intro edge _
  congr 1
  funext ω
  cases hc : R.crosses ω <;> simp [conditioning, disconnectedOpenEdgeIndicator, hc]

theorem closed_state_indicator_sum (σ : LiveState) (ω : Configuration edges) (edge : Fin edges) :
    (if R.childState σ ω edge = some .both then (1 : ℝ) else 0) +
      (if R.childState σ ω edge = some .single then 1 else 0) =
        if R.childState σ ω edge = some .both ∨ R.childState σ ω edge = some .single then 1 else 0 := by
  cases h : R.childState σ ω edge with
  | none => simp
  | some state => cases state <;> simp

theorem connected_closed_edge_sum (p : ℝ) :
    R.countingMoment p .connected .both + R.countingMoment p .connected .single =
      ∑ edge, expectation p (fun ω => R.connectedClosedEdgeIndicator ω edge) := by
  rw [countingMoment_as_edge_sum, countingMoment_as_edge_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [expectation, ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  intro ω _
  cases hc : R.crosses ω <;>
    simp [conditioning, connectedClosedEdgeIndicator, hc, R.closed_state_indicator_sum]

theorem disconnected_closed_edge_sum (p : ℝ) :
    R.countingMoment p .single .both + R.countingMoment p .single .single =
      ∑ edge, expectation p (fun ω => R.disconnectedClosedEdgeIndicator ω edge) := by
  rw [countingMoment_as_edge_sum, countingMoment_as_edge_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [expectation, ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  intro ω _
  cases hc : R.crosses ω <;>
    simp [conditioning, disconnectedClosedEdgeIndicator, hc, R.closed_state_indicator_sum]

theorem connected_counting_identity (p : ℝ) :
    (1 - p) * R.countingMoment p .connected .connected -
      p * (R.countingMoment p .connected .both + R.countingMoment p .connected .single) =
        p * (1 - p) * deriv R.reliability p := by
  rw [connected_open_edge_sum, connected_closed_edge_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  simp_rw [R.expected_connected_edge_score]
  rw [← Finset.mul_sum, R.expectation_pivotalCount, R.russo_formula]

theorem disconnected_counting_identity (p : ℝ) :
    (1 - p) * R.countingMoment p .single .connected -
      p * (R.countingMoment p .single .both + R.countingMoment p .single .single) =
        -(p * (1 - p) * deriv R.reliability p) := by
  rw [disconnected_open_edge_sum, disconnected_closed_edge_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  simp_rw [R.expected_disconnected_edge_score]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, R.expectation_pivotalCount, R.russo_formula]

end
end Universality.FiniteNetwork
