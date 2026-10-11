import Universality.Matrix.PivotalRightVector

namespace Universality
noncomputable section
open Matrix FiniteNetwork

def criticalBasis (p : ℝ) : Matrix LiveState LiveState ℝ
  | .connected, .connected => 1
  | .both, .connected | .single, .connected => 0
  | .connected, .both => 0
  | .both, .both => 2
  | .single, .both => 1
  | .connected, .single => 1 - p
  | .both, .single | .single, .single => -p

def criticalBasisInverse (p : ℝ) : Matrix LiveState LiveState ℝ
  | .connected, .connected => 1
  | .connected, .both => -(1 - p) / p
  | .connected, .single => 2 * (1 - p) / p
  | .both, .connected | .single, .connected => 0
  | .both, .both => 1
  | .both, .single => -1
  | .single, .both => 1 / p
  | .single, .single => -2 / p

def criticalBlock (M : Matrix LiveState LiveState ℝ) (response : ℝ) :
    Matrix LiveState LiveState ℝ
  | .connected, .connected => massPlaneBlock M 0 0
  | .connected, .both => massPlaneBlock M 0 1
  | .both, .connected => massPlaneBlock M 1 0
  | .both, .both => massPlaneBlock M 1 1
  | .single, .single => response
  | _, _ => 0

theorem criticalBasisInverse_mul (p : ℝ) (hne : p ≠ 0) :
    criticalBasisInverse p * criticalBasis p = 1 := by
  have hcb : LiveState.connected ≠ .both := by decide
  have hcu : LiveState.connected ≠ .single := by decide
  have hbu : LiveState.both ≠ .single := by decide
  ext σ τ
  cases σ <;> cases τ <;>
    norm_num [Matrix.mul_apply, sum_liveState, criticalBasis, criticalBasisInverse,
      Matrix.one_apply, hne, hcb, hcu, hbu, Ne.symm hcb, Ne.symm hcu, Ne.symm hbu] <;>
      field_simp <;> ring

theorem criticalBasis_mul_inverse (p : ℝ) (hne : p ≠ 0) :
    criticalBasis p * criticalBasisInverse p = 1 := by
  have hcb : LiveState.connected ≠ .both := by decide
  have hcu : LiveState.connected ≠ .single := by decide
  have hbu : LiveState.both ≠ .single := by decide
  ext σ τ
  cases σ <;> cases τ <;>
    norm_num [Matrix.mul_apply, sum_liveState, criticalBasis, criticalBasisInverse,
      Matrix.one_apply, hne, hcb, hcu, hbu, Ne.symm hcb, Ne.symm hcu, Ne.symm hbu] <;>
      field_simp <;> ring

theorem criticalBlock_intertwining (M : Matrix LiveState LiveState ℝ) (p response : ℝ)
    (hplane : PreservesMassPlane M)
    (heigen : M *ᵥ pivotalRightVector p = response • pivotalRightVector p) :
    M * criticalBasis p = criticalBasis p * criticalBlock M response := by
  have hfirst := hplane ![1, 0]
  have hsecond := hplane ![0, 1]
  ext σ τ
  have hf := congrFun hfirst σ
  have hs := congrFun hsecond σ
  have he := congrFun heigen σ
  cases τ <;> cases σ <;>
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, sum_liveState, criticalBasis,
      criticalBlock, massPlaneBlock, massPlaneLift, pivotalRightVector, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul] at hf hs he ⊢ <;> nlinarith

theorem criticalBlock_conjugation (M : Matrix LiveState LiveState ℝ) (p response : ℝ)
    (hne : p ≠ 0) (hplane : PreservesMassPlane M)
    (heigen : M *ᵥ pivotalRightVector p = response • pivotalRightVector p) :
    criticalBasisInverse p * M * criticalBasis p = criticalBlock M response := by
  rw [Matrix.mul_assoc, criticalBlock_intertwining M p response hplane heigen,
    ← Matrix.mul_assoc, criticalBasisInverse_mul p hne, Matrix.one_mul]

theorem criticalBlock_reconstruction (M : Matrix LiveState LiveState ℝ) (p response : ℝ)
    (hne : p ≠ 0) (hplane : PreservesMassPlane M)
    (heigen : M *ᵥ pivotalRightVector p = response • pivotalRightVector p) :
    M = criticalBasis p * criticalBlock M response * criticalBasisInverse p := by
  rw [← criticalBlock_intertwining M p response hplane heigen,
    Matrix.mul_assoc, criticalBasis_mul_inverse p hne, Matrix.mul_one]

theorem criticalBlock_power_intertwining (M : Matrix LiveState LiveState ℝ) (p response : ℝ)
    (hplane : PreservesMassPlane M)
    (heigen : M *ᵥ pivotalRightVector p = response • pivotalRightVector p) (n : ℕ) :
    M ^ n * criticalBasis p = criticalBasis p * criticalBlock M response ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_assoc, criticalBlock_intertwining M p response hplane heigen,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

theorem criticalBlock_power_reconstruction (M : Matrix LiveState LiveState ℝ)
    (p response : ℝ) (hne : p ≠ 0) (hplane : PreservesMassPlane M)
    (heigen : M *ᵥ pivotalRightVector p = response • pivotalRightVector p) (n : ℕ) :
    M ^ n = criticalBasis p * criticalBlock M response ^ n * criticalBasisInverse p := by
  rw [← criticalBlock_power_intertwining M p response hplane heigen,
    Matrix.mul_assoc, criticalBasis_mul_inverse p hne, Matrix.mul_one]

namespace FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem massMatrix_critical_block_decomposition (p : ℝ) (hfixed : R.reliability p = p)
    (hne : p ≠ 0) (hne' : p ≠ 1) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    criticalBasisInverse p * R.massMatrix p * criticalBasis p =
      criticalBlock (R.massMatrix p) (deriv R.reliability p) := by
  apply criticalBlock_conjugation _ _ _ hne
  · exact R.massMatrix_preservesMassPlane p symmetry hs ht
  · exact R.pivotal_right_eigenvector_at_fixed_point p hfixed hne hne' symmetry hs ht

end FiniteNetwork
end
end Universality
