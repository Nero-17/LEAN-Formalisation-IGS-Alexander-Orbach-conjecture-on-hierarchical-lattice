import Universality.Percolation.EdgeResampling
import Universality.Percolation.ReliabilityDerivative

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem crosses_mono (ω ν : Configuration edges)
    (hopen : ∀ edge, ω edge = true → ν edge = true) :
    R.crosses ω = true → R.crosses ν = true := by
  intro hcross
  apply (R.crosses_eq_true ν).mpr
  apply ((R.crosses_eq_true ω).mp hcross).mono
  intro u v hadj
  obtain ⟨hne, edge, he, hpair⟩ := hadj
  exact ⟨hne, edge, hopen edge he, hpair⟩

theorem crosses_update_false_le_true (ω : Configuration edges) (edge : Fin edges) :
    R.crosses (Function.update ω edge false) = true →
      R.crosses (Function.update ω edge true) = true := by
  apply R.crosses_mono
  intro other hother
  by_cases heq : other = edge
  · subst other
    simp
  · simpa [Function.update_of_ne heq] using hother

def pivotal (ω : Configuration edges) (edge : Fin edges) : Bool :=
  R.crosses (Function.update ω edge true) && !R.crosses (Function.update ω edge false)

def pivotalCount (ω : Configuration edges) : ℕ :=
  (Finset.univ.filter fun edge => R.pivotal ω edge = true).card

def crossingIndicator (ω : Configuration edges) : ℝ := if R.crosses ω then 1 else 0

theorem crossingIndicator_difference (ω : Configuration edges) (edge : Fin edges) :
    R.crossingIndicator (Function.update ω edge true) -
      R.crossingIndicator (Function.update ω edge false) =
      if R.pivotal ω edge then 1 else 0 := by
  have hmono := R.crosses_update_false_le_true ω edge
  unfold crossingIndicator pivotal
  cases ht : R.crosses (Function.update ω edge true) <;>
    cases hf : R.crosses (Function.update ω edge false) <;> norm_num
  have h := hmono hf
  rw [ht] at h
  contradiction

theorem expectation_crossingIndicator (p : ℝ) :
    expectation p R.crossingIndicator = R.reliability p := by
  simp only [expectation, crossingIndicator, reliability, mul_ite, mul_one, mul_zero]

theorem expectation_pivotalCount (p : ℝ) :
    (∑ edge : Fin edges, expectation p (fun ω => if R.pivotal ω edge then 1 else 0)) =
      expectation p (fun ω => R.pivotalCount ω) := by
  unfold expectation pivotalCount
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem hasDerivAt_reliability_expected_pivotalCount (p : ℝ) :
    HasDerivAt R.reliability (expectation p (fun ω => R.pivotalCount ω)) p := by
  have h := hasDerivAt_expectation_resampling R.crossingIndicator p
  simp_rw [R.crossingIndicator_difference] at h
  rw [R.expectation_pivotalCount] at h
  have hfunction : (fun p => expectation p R.crossingIndicator) = R.reliability :=
    funext R.expectation_crossingIndicator
  rw [hfunction] at h
  exact h

theorem russo_formula (p : ℝ) :
    deriv R.reliability p = expectation p (fun ω => R.pivotalCount ω) :=
  (R.hasDerivAt_reliability_expected_pivotalCount p).deriv

theorem pivotal_update (ω : Configuration edges) (edge : Fin edges) (opened : Bool) :
    R.pivotal (Function.update ω edge opened) edge = R.pivotal ω edge := by
  simp [pivotal]

end
end Universality.FiniteNetwork
