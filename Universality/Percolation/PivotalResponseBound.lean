import Universality.Percolation.StrictInstability

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0

def openEdgeSum {edges : ℕ} (ω : Configuration edges) : ℝ :=
  ∑ edge, if ω edge then 1 else 0

theorem openEdgeSum_cons {edges : ℕ} (opened : Bool) (ω : Configuration edges) :
    openEdgeSum (Fin.cons opened ω) = (if opened then 1 else 0) + openEdgeSum ω := by
  simp only [openEdgeSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem expectation_openEdgeSum (edges : ℕ) (p : ℝ) :
    expectation p (@openEdgeSum edges) = edges * p := by
  induction edges with
  | zero => simp [expectation, openEdgeSum]
  | succ edges ih =>
    rw [expectation_cons]
    simp only [openEdgeSum_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [expectation_add, expectation_const, ih]
    push_cast
    ring

theorem variance_openEdgeSum (edges : ℕ) (p : ℝ) :
    bernoulliVariance p (@openEdgeSum edges) = edges * p * (1 - p) := by
  induction edges with
  | zero => simp [bernoulliVariance, expectation, openEdgeSum]
  | succ edges ih =>
    rw [variance_cons]
    simp only [openEdgeSum_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
    have hshift : bernoulliVariance p (fun ω : Configuration edges => 1 + openEdgeSum ω) =
        bernoulliVariance p (@openEdgeSum edges) := by
      rw [bernoulliVariance_eq_centered_square, bernoulliVariance_eq_centered_square,
        expectation_add, expectation_const]
      congr 1
      funext ω
      congr 1
      ring
    rw [hshift, ih, expectation_add, expectation_const, expectation_openEdgeSum]
    push_cast
    ring

theorem edge_crossing_covariance {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) (edge : Fin edges) :
    expectation p (fun ω => R.crossingIndicator ω * ((if ω edge then 1 else 0) - p)) =
      p * (1 - p) * expectation p (fun ω => if R.pivotal ω edge then 1 else 0) := by
  simp_rw [← R.crossingIndicator_difference]
  unfold expectation
  rw [sum_splitConfiguration edge, sum_splitConfiguration edge, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  simp only [bernoulliWeight_insertEdge, insertEdge_self, update_insertEdge,
    Bool.false_eq_true, ↓reduceIte]
  ring

theorem crossing_openEdgeSum_covariance {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) :
    expectation p (fun ω => R.crossingIndicator ω * openEdgeSum ω) -
      R.reliability p * (edges * p) = p * (1 - p) * deriv R.reliability p := by
  have h := congrArg (fun f : Fin edges → ℝ => ∑ edge, f edge)
    (funext (R.edge_crossing_covariance p))
  rw [← Finset.mul_sum, R.expectation_pivotalCount, ← R.russo_formula] at h
  rw [← h]
  have hterm (edge : Fin edges) :
      expectation p (fun ω => R.crossingIndicator ω * ((if ω edge then 1 else 0) - p)) =
      expectation p (fun ω => R.crossingIndicator ω * (if ω edge then 1 else 0)) -
        R.reliability p * p := by
    simp only [mul_sub, expectation_sub, expectation_mul_const, R.expectation_crossingIndicator]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ edge : Fin edges,
      expectation p (fun ω => R.crossingIndicator ω * (if ω edge then 1 else 0))) =
      expectation p (fun ω => R.crossingIndicator ω * openEdgeSum ω) := by
    simp only [expectation, openEdgeSum, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem variance_linear_combination {edges : ℕ} (p a b : ℝ)
    (first second : Configuration edges → ℝ) :
    bernoulliVariance p (fun ω => a * first ω - b * second ω) =
      a ^ 2 * bernoulliVariance p first + b ^ 2 * bernoulliVariance p second -
        2 * a * b * (expectation p (fun ω => first ω * second ω) -
          expectation p first * expectation p second) := by
  have hexpand : (fun ω => (a * first ω - b * second ω) ^ 2) =
      fun ω => a ^ 2 * first ω ^ 2 + b ^ 2 * second ω ^ 2 -
        (2 * a * b) * (first ω * second ω) := by funext ω; ring
  simp only [bernoulliVariance, hexpand, expectation_sub, expectation_add,
    expectation_const_mul]
  ring

/-- The strict response bound added to Section 2. Its proof uses the actual
Bernoulli covariance, with strictness witnessed by empty and singleton states. -/
theorem pivotal_response_sq_lt_edges {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : R.reliability p = p)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    (deriv R.reliability p) ^ 2 < edges := by
  have hderiv := R.interior_fixed_point_strictly_unstable p hp hp' hfixed hscale
  have hedges : 0 < edges := by
    by_contra h
    have hz : edges = 0 := by omega
    subst edges
    have hconfig : ∀ ω : Configuration 0, ω = (fun _ => false) := by
      intro ω
      funext edge
      exact edge.elim0
    have hz : R.reliability p = 0 := by
      simp [reliability, hconfig, R.crosses_all_closed]
    linarith
  have hvar := bernoulliVariance_pos_of_ne hp hp'
    (fun ω => (edges : ℝ) * R.crossingIndicator ω - deriv R.reliability p * openEdgeSum ω)
    (fun _ => false) (onlyOpen ⟨0, hedges⟩) (by
      simp only [crossingIndicator, R.crosses_all_closed,
        R.crosses_onlyOpen_false_of_scale _ hscale, Bool.false_eq_true, ↓reduceIte,
        mul_zero, openEdgeSum]
      simp [onlyOpen, Function.update_apply]
      linarith)
  rw [variance_linear_combination, R.crossing_variance, variance_openEdgeSum,
    R.expectation_crossingIndicator, expectation_openEdgeSum,
    R.crossing_openEdgeSum_covariance, hfixed] at hvar
  have hepos : (0 : ℝ) < edges := Nat.cast_pos.mpr hedges
  have hfactor : 0 < (edges : ℝ) * p * (1 - p) :=
    mul_pos (mul_pos hepos hp) (sub_pos.mpr hp')
  have hfinal : 0 < (edges : ℝ) * p * (1 - p) *
      ((edges : ℝ) - (deriv R.reliability p) ^ 2) := by nlinarith [hvar]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hfactor).mp hfinal)

end
end Universality.FiniteNetwork
