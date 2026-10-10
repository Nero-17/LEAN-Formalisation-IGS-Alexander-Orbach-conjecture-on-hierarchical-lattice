import Universality.Matrix.UniversalPivotalVector
import Universality.Percolation.EdgeScoreIdentities

namespace Universality.FiniteNetwork
noncomputable section
open Matrix

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem massMatrix_countingMoment (p : ℝ) (σ τ : LiveState) :
    R.massMatrix p σ τ = R.countingMoment p σ τ / R.conditioningProbability p σ := rfl

theorem connected_mass_score_at_fixed_point (p : ℝ) (hfixed : R.reliability p = p)
    (hne : p ≠ 0) :
    (1 - p) * R.massMatrix p .connected .connected -
      p * (R.massMatrix p .connected .both + R.massMatrix p .connected .single) =
        (1 - p) * deriv R.reliability p := by
  simp only [massMatrix_countingMoment, conditioningProbability_connected, hfixed]
  have h := R.connected_counting_identity p
  field_simp
  nlinarith

theorem disconnected_mass_score_at_fixed_point (p : ℝ) (hfixed : R.reliability p = p)
    (hne : p ≠ 1) :
    (1 - p) * R.massMatrix p .single .connected -
      p * (R.massMatrix p .single .both + R.massMatrix p .single .single) =
        -p * deriv R.reliability p := by
  simp only [massMatrix_countingMoment, conditioningProbability_single, hfixed]
  have h := R.disconnected_counting_identity p
  have hdenom : 1 - p ≠ 0 := sub_ne_zero.mpr hne.symm
  field_simp
  nlinarith

def pivotalRightVector (p : ℝ) : LiveState → ℝ
  | .connected => 1 - p
  | .both | .single => -p

theorem pivotal_right_eigenvector_at_fixed_point (p : ℝ) (hfixed : R.reliability p = p)
    (hne : p ≠ 0) (hne' : p ≠ 1) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    R.massMatrix p *ᵥ pivotalRightVector p = deriv R.reliability p • pivotalRightVector p := by
  have hc := R.connected_mass_score_at_fixed_point p hfixed hne
  have hu := R.disconnected_mass_score_at_fixed_point p hfixed hne'
  have hrow (τ : LiveState) : R.massMatrix p .both τ = 2 * R.massMatrix p .single τ +
      pivotalRowCorrection τ * deriv R.reliability p := by
    have h := R.massMatrix_row_identity p symmetry hs ht τ
    rw [hfixed, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hne'.symm)] at h
    exact h
  ext σ
  simp only [Matrix.mulVec, dotProduct, sum_liveState, pivotalRightVector,
    Pi.smul_apply, smul_eq_mul]
  cases σ
  · simp only [pivotalRightVector]
    nlinarith
  · simp only [pivotalRightVector]
    rw [hrow .connected, hrow .both, hrow .single]
    simp only [pivotalRowCorrection]
    nlinarith
  · simp only [pivotalRightVector]
    nlinarith

end
end Universality.FiniteNetwork
