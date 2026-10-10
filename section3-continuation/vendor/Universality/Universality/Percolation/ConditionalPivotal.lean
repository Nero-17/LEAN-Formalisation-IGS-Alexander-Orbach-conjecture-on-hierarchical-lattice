import Universality.Percolation.Russo

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem pivotal_crosses_eq_state (ω : Configuration edges) (edge : Fin edges)
    (hpivotal : R.pivotal ω edge = true) : R.crosses ω = ω edge := by
  have hparts : R.crosses (Function.update ω edge true) = true ∧
      R.crosses (Function.update ω edge false) = false := by
    simpa only [pivotal, Bool.and_eq_true, Bool.not_eq_true'] using hpivotal
  obtain ⟨hopen, hclosed'⟩ := hparts
  have hself := Function.update_eq_self edge ω
  cases hstate : ω edge
  · rw [hstate] at hself
    rwa [hself] at hclosed'
  · rw [hstate] at hself
    rwa [hself] at hopen

theorem connected_pivotal_indicator (ω : Configuration edges) (edge : Fin edges) :
    (if R.crosses ω then (if R.pivotal ω edge then (1 : ℝ) else 0) else 0) =
      if ω edge then (if R.pivotal ω edge then 1 else 0) else 0 := by
  by_cases h : R.pivotal ω edge = true
  · rw [R.pivotal_crosses_eq_state ω edge h]
  · simp [h]

theorem disconnected_pivotal_indicator (ω : Configuration edges) (edge : Fin edges) :
    (if R.crosses ω then (0 : ℝ) else (if R.pivotal ω edge then 1 else 0)) =
      if ω edge then 0 else (if R.pivotal ω edge then 1 else 0) := by
  by_cases h : R.pivotal ω edge = true
  · rw [R.pivotal_crosses_eq_state ω edge h]
  · simp [h]

theorem expected_connected_pivotal_edge (p : ℝ) (edge : Fin edges) :
    expectation p (fun ω => if R.crosses ω then (if R.pivotal ω edge then 1 else 0) else 0) =
      p * expectation p (fun ω => if R.pivotal ω edge then 1 else 0) := by
  simp_rw [connected_pivotal_indicator]
  apply expectation_open_independent
  intro ω opened
  rw [R.pivotal_update]

theorem expected_disconnected_pivotal_edge (p : ℝ) (edge : Fin edges) :
    expectation p (fun ω => if R.crosses ω then 0 else (if R.pivotal ω edge then 1 else 0)) =
      (1 - p) * expectation p (fun ω => if R.pivotal ω edge then 1 else 0) := by
  simp_rw [disconnected_pivotal_indicator]
  apply expectation_closed_independent
  intro ω opened
  rw [R.pivotal_update]

theorem pivotalCount_as_sum (ω : Configuration edges) :
    (R.pivotalCount ω : ℝ) = ∑ edge : Fin edges, if R.pivotal ω edge then 1 else 0 := by
  simp only [pivotalCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem expectation_sum {ι : Type*} [Fintype ι]
    (p : ℝ) (responses : ι → Configuration edges → ℝ) :
    expectation p (fun ω => ∑ i, responses i ω) = ∑ i, expectation p (responses i) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expected_connected_pivotalCount (p : ℝ) :
    expectation p (fun ω => if R.crosses ω then (R.pivotalCount ω : ℝ) else 0) =
      p * deriv R.reliability p := by
  simp_rw [R.pivotalCount_as_sum]
  have distribute (ω : Configuration edges) :
      (if R.crosses ω then ∑ edge, (if R.pivotal ω edge then (1 : ℝ) else 0) else 0) =
        ∑ edge : Fin edges, if R.crosses ω then (if R.pivotal ω edge then 1 else 0) else 0 := by
    cases R.crosses ω <;> simp
  simp_rw [distribute]
  rw [expectation_sum]
  simp_rw [R.expected_connected_pivotal_edge]
  rw [← Finset.mul_sum, R.expectation_pivotalCount, R.russo_formula]

theorem expected_disconnected_pivotalCount (p : ℝ) :
    expectation p (fun ω => if R.crosses ω then (0 : ℝ) else R.pivotalCount ω) =
      (1 - p) * deriv R.reliability p := by
  simp_rw [R.pivotalCount_as_sum]
  have distribute (ω : Configuration edges) :
      (if R.crosses ω then (0 : ℝ) else ∑ edge, (if R.pivotal ω edge then 1 else 0)) =
        ∑ edge : Fin edges, if R.crosses ω then 0 else (if R.pivotal ω edge then 1 else 0) := by
    cases R.crosses ω <;> simp
  simp_rw [distribute]
  rw [expectation_sum]
  simp_rw [R.expected_disconnected_pivotal_edge]
  rw [← Finset.mul_sum, R.expectation_pivotalCount, R.russo_formula]

theorem conditional_connected_pivotalCount_at_fixed_point (p : ℝ)
    (hfixed : R.reliability p = p) (hne : p ≠ 0) :
    expectation p (fun ω => if R.crosses ω then (R.pivotalCount ω : ℝ) else 0) /
      R.reliability p = deriv R.reliability p := by
  rw [R.expected_connected_pivotalCount, hfixed, mul_div_cancel_left₀ _ hne]

theorem conditional_disconnected_pivotalCount (p : ℝ) :
    expectation p (fun ω => if R.crosses ω then (0 : ℝ) else R.pivotalCount ω) /
      (1 - R.reliability p) = (1 - p) * deriv R.reliability p / (1 - R.reliability p) := by
  rw [R.expected_disconnected_pivotalCount]

end
end Universality.FiniteNetwork
