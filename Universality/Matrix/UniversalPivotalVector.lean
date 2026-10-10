import Universality.Percolation.StateRowIdentities
import Universality.Matrix.WheatstoneSpectrum

namespace Universality.FiniteNetwork
noncomputable section
open Matrix

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem expected_disconnected_liveCount_row (p : ℝ) (τ : LiveState) :
    expectation p (fun ω => if R.crosses ω then (0 : ℝ) else R.liveCount .both τ ω) =
      expectation p (fun ω => if R.crosses ω then (0 : ℝ) else R.liveCount .single τ ω) +
      expectation p (fun ω => if R.crosses ω then (0 : ℝ) else R.reverse.liveCount .single τ ω) +
        pivotalRowCorrection τ * ((1 - p) * deriv R.reliability p) := by
  have hpoint (ω : Configuration edges) :
      (if R.crosses ω then (0 : ℝ) else R.liveCount .both τ ω) =
        (if R.crosses ω then (0 : ℝ) else R.liveCount .single τ ω) +
        (if R.crosses ω then (0 : ℝ) else R.reverse.liveCount .single τ ω) +
        pivotalRowCorrection τ * (if R.crosses ω then (0 : ℝ) else R.pivotalCount ω) := by
    cases hc : R.crosses ω
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact R.liveCount_row_identity ω hc τ
    · simp
  rw [← R.expected_disconnected_pivotalCount]
  simp only [expectation, hpoint, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 2
  funext ω
  ring

theorem massMatrix_both_disconnected (p : ℝ) (τ : LiveState) :
    R.massMatrix p .both τ =
      expectation p (fun ω => if R.crosses ω then (0 : ℝ) else R.liveCount .both τ ω) /
        (1 - R.reliability p) := by
  unfold massMatrix
  rw [R.conditioningProbability_both]
  congr 1
  unfold expectation
  apply Finset.sum_congr rfl
  intro ω _
  unfold conditioning
  cases hc : R.crosses ω <;> simp [hc]

theorem massMatrix_single_disconnected (p : ℝ) (τ : LiveState) :
    R.massMatrix p .single τ =
      expectation p (fun ω => if R.crosses ω then (0 : ℝ) else R.liveCount .single τ ω) /
        (1 - R.reliability p) := by
  unfold massMatrix
  rw [R.conditioningProbability_single]
  congr 1
  unfold expectation
  apply Finset.sum_congr rfl
  intro ω _
  unfold conditioning
  cases hc : R.crosses ω <;> simp [hc]

theorem massMatrix_row_identity_with_reverse (p : ℝ) (τ : LiveState) :
    R.massMatrix p .both τ = R.massMatrix p .single τ + R.reverse.massMatrix p .single τ +
      pivotalRowCorrection τ * ((1 - p) * deriv R.reliability p / (1 - R.reliability p)) := by
  rw [massMatrix_both_disconnected, massMatrix_single_disconnected,
    massMatrix_single_disconnected, reliability_reverse]
  simp_rw [crosses_reverse]
  rw [expected_disconnected_liveCount_row]
  ring

theorem massMatrix_row_identity (p : ℝ) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (τ : LiveState) :
    R.massMatrix p .both τ = 2 * R.massMatrix p .single τ +
      pivotalRowCorrection τ * ((1 - p) * deriv R.reliability p / (1 - R.reliability p)) := by
  rw [massMatrix_row_identity_with_reverse, symmetry.massMatrix_reverse hs ht]
  ring

/-- The exact off-critical left eigenvalue; at a fixed point it reduces
to the derivative, provided the fixed point is not one. -/
theorem pivotal_left_eigenvector (p : ℝ) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    pivotalLeftVector ᵥ* R.massMatrix p =
      ((1 - p) * deriv R.reliability p / (1 - R.reliability p)) • pivotalLeftVector := by
  ext τ
  have h := R.massMatrix_row_identity p symmetry hs ht τ
  simp only [Matrix.vecMul, dotProduct, sum_liveState, pivotalLeftVector,
    zero_mul, one_mul, zero_add, Pi.smul_apply, smul_eq_mul]
  cases τ <;> simp only [pivotalRowCorrection] at h ⊢ <;> linarith

theorem pivotal_left_eigenvector_at_fixed_point (p : ℝ) (hfixed : R.reliability p = p)
    (hne : p ≠ 1) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    pivotalLeftVector ᵥ* R.massMatrix p = deriv R.reliability p • pivotalLeftVector := by
  rw [pivotal_left_eigenvector R p symmetry hs ht, hfixed,
    mul_div_cancel_left₀ _ (sub_ne_zero.mpr hne.symm)]

theorem massMatrix_preservesMassPlane (p : ℝ) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    PreservesMassPlane (R.massMatrix p) := by
  apply preservesMassPlane_of_entries
  · simpa only [pivotalRowCorrection, zero_mul, add_zero] using
      R.massMatrix_row_identity p symmetry hs ht .connected
  · have hb := R.massMatrix_row_identity p symmetry hs ht .both
    have hu := R.massMatrix_row_identity p symmetry hs ht .single
    simp only [pivotalRowCorrection] at hb hu
    linarith

end
end Universality.FiniteNetwork
