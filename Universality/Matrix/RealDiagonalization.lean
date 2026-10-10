import Universality.Matrix.CriticalBlockDecomposition
import Universality.Matrix.TwoByTwoExpansion

namespace Universality
noncomputable section
open Matrix FiniteNetwork

def blockEigenbasis (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix LiveState LiveState ℝ
  | .connected, .connected | .connected, .both => A 0 1
  | .both, .connected => positiveRoot A - A 0 0
  | .both, .both => secondaryRoot A - A 0 0
  | .single, .single => 1
  | _, _ => 0

def blockEigenbasisInverse (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix LiveState LiveState ℝ
  | .connected, .connected =>
      (secondaryRoot A - A 0 0) / (A 0 1 * (secondaryRoot A - positiveRoot A))
  | .connected, .both => -1 / (secondaryRoot A - positiveRoot A)
  | .both, .connected =>
      -(positiveRoot A - A 0 0) / (A 0 1 * (secondaryRoot A - positiveRoot A))
  | .both, .both => 1 / (secondaryRoot A - positiveRoot A)
  | .single, .single => 1
  | _, _ => 0

def blockEigenvalues (A : Matrix (Fin 2) (Fin 2) ℝ) (response : ℝ) : LiveState → ℝ
  | .connected => positiveRoot A
  | .both => secondaryRoot A
  | .single => response

theorem blockEigenbasisInverse_mul (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : blockEigenbasisInverse A * blockEigenbasis A = 1 := by
  have hb := (hA 0 1).ne'
  have hd : secondaryRoot A - positiveRoot A ≠ 0 :=
    (sub_neg.mpr (by linarith [positiveRoot_sub_secondary_pos A hA])).ne
  have hcb : LiveState.connected ≠ .both := by decide
  have hcu : LiveState.connected ≠ .single := by decide
  have hbu : LiveState.both ≠ .single := by decide
  ext σ τ
  cases σ <;> cases τ <;>
    norm_num [Matrix.mul_apply, sum_liveState, blockEigenbasis, blockEigenbasisInverse,
      Matrix.one_apply, hcb, hcu, hbu, Ne.symm hcb, Ne.symm hcu, Ne.symm hbu] <;>
      field_simp <;> ring

theorem blockEigenbasis_mul_inverse (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : blockEigenbasis A * blockEigenbasisInverse A = 1 := by
  have hb := (hA 0 1).ne'
  have hd : secondaryRoot A - positiveRoot A ≠ 0 :=
    (sub_neg.mpr (by linarith [positiveRoot_sub_secondary_pos A hA])).ne
  have hcb : LiveState.connected ≠ .both := by decide
  have hcu : LiveState.connected ≠ .single := by decide
  have hbu : LiveState.both ≠ .single := by decide
  ext σ τ
  cases σ <;> cases τ <;>
    norm_num [Matrix.mul_apply, sum_liveState, blockEigenbasis, blockEigenbasisInverse,
      Matrix.one_apply, hcb, hcu, hbu, Ne.symm hcb, Ne.symm hcu, Ne.symm hbu] <;>
      field_simp <;> ring

theorem secondaryRoot_quadratic (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : secondaryRoot A ^ 2 - A.trace * secondaryRoot A + A.det = 0 := by
  have hsum := root_sum A
  have hprod := root_product A hA
  rw [← hsum, ← hprod]
  ring

theorem blockEigenbasis_intertwining (M : Matrix LiveState LiveState ℝ) (response : ℝ)
    (hblock : ∀ i j, 0 < massPlaneBlock M i j) :
    criticalBlock M response * blockEigenbasis (massPlaneBlock M) =
      blockEigenbasis (massPlaneBlock M) * Matrix.diagonal (blockEigenvalues (massPlaneBlock M) response) := by
  have hr := positiveRoot_quadratic (massPlaneBlock M) hblock
  have hs := secondaryRoot_quadratic (massPlaneBlock M) hblock
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hr hs
  ext σ τ
  cases σ <;> cases τ <;>
    simp [Matrix.mul_apply, sum_liveState, criticalBlock, blockEigenbasis,
      Matrix.diagonal_apply, blockEigenvalues] <;> nlinarith

/-- Explicit real diagonalisation, valid even if the response eigenvalue
coincides with the smaller eigenvalue of the positive block. -/
theorem real_diagonalization_of_critical_block (M : Matrix LiveState LiveState ℝ)
    (p response : ℝ) (hne : p ≠ 0) (hplane : PreservesMassPlane M)
    (heigen : M *ᵥ pivotalRightVector p = response • pivotalRightVector p)
    (hblock : ∀ i j, 0 < massPlaneBlock M i j) :
    ∃ basis inverse : Matrix LiveState LiveState ℝ,
      inverse * basis = 1 ∧ basis * inverse = 1 ∧
      inverse * M * basis = Matrix.diagonal (blockEigenvalues (massPlaneBlock M) response) := by
  refine ⟨criticalBasis p * blockEigenbasis (massPlaneBlock M),
    blockEigenbasisInverse (massPlaneBlock M) * criticalBasisInverse p, ?_, ?_, ?_⟩
  · calc
      _ = blockEigenbasisInverse (massPlaneBlock M) *
          (criticalBasisInverse p * criticalBasis p) * blockEigenbasis (massPlaneBlock M) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [criticalBasisInverse_mul p hne, Matrix.mul_one,
        blockEigenbasisInverse_mul _ hblock]
  · calc
      _ = criticalBasis p * (blockEigenbasis (massPlaneBlock M) *
          blockEigenbasisInverse (massPlaneBlock M)) * criticalBasisInverse p := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [blockEigenbasis_mul_inverse _ hblock, Matrix.mul_one,
        criticalBasis_mul_inverse p hne]
  · calc
      _ = blockEigenbasisInverse (massPlaneBlock M) *
          (criticalBasisInverse p * M * criticalBasis p) * blockEigenbasis (massPlaneBlock M) := by
            simp only [Matrix.mul_assoc]
      _ = blockEigenbasisInverse (massPlaneBlock M) *
          criticalBlock M response * blockEigenbasis (massPlaneBlock M) := by
            rw [criticalBlock_conjugation M p response hne hplane heigen]
      _ = _ := by
        rw [Matrix.mul_assoc, blockEigenbasis_intertwining M response hblock,
          ← Matrix.mul_assoc, blockEigenbasisInverse_mul _ hblock, Matrix.one_mul]

namespace FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem massMatrix_real_diagonalization (p : ℝ) (hfixed : R.reliability p = p)
    (hp : 0 < p) (hp' : p < 1) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (hblock : ∀ i j, 0 < massPlaneBlock (R.massMatrix p) i j) :
    ∃ basis inverse : Matrix LiveState LiveState ℝ,
      inverse * basis = 1 ∧ basis * inverse = 1 ∧
      inverse * R.massMatrix p * basis =
        Matrix.diagonal (blockEigenvalues (massPlaneBlock (R.massMatrix p)) (deriv R.reliability p)) := by
  apply real_diagonalization_of_critical_block _ _ _ hp.ne'
    (R.massMatrix_preservesMassPlane p symmetry hs ht)
    (R.pivotal_right_eigenvector_at_fixed_point p hfixed hp.ne' hp'.ne symmetry hs ht) hblock

end FiniteNetwork
end
end Universality
