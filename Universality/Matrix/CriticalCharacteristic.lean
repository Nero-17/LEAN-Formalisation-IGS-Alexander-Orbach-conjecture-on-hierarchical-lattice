import Universality.Percolation.CriticalField
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace Universality
noncomputable section
open Matrix FiniteNetwork Polynomial

def liveStateEnumeration : Fin 3 ≃ LiveState where
  toFun := ![.connected, .both, .single]
  invFun
    | .connected => 0
    | .both => 1
    | .single => 2
  left_inv i := by fin_cases i <;> rfl
  right_inv σ := by cases σ <;> rfl

theorem criticalBasis_det (p : ℝ) : (criticalBasis p).det = -p := by
  rw [← Matrix.det_submatrix_equiv_self liveStateEnumeration, Matrix.det_fin_three]
  simp [Matrix.submatrix, liveStateEnumeration, criticalBasis]
  ring

theorem criticalBlock_charpoly (M : Matrix LiveState LiveState ℝ) (response : ℝ) :
    (criticalBlock M response).charpoly =
      (X - C response) * (X ^ 2 - C (Matrix.trace (massPlaneBlock M)) * X +
        C (Matrix.det (massPlaneBlock M))) := by
  rw [Matrix.charpoly, ← Matrix.det_submatrix_equiv_self liveStateEnumeration,
    Matrix.det_fin_three]
  simp [Matrix.submatrix, liveStateEnumeration, Matrix.charmatrix_apply,
    Matrix.diagonal_apply, criticalBlock, Matrix.trace, Fin.sum_univ_two,
    Matrix.det_fin_two, map_add, map_sub, map_mul]
  ring

theorem critical_charpoly (M : Matrix LiveState LiveState ℝ) (p response : ℝ)
    (hp : p ≠ 0) (hplane : PreservesMassPlane M)
    (heigen : M *ᵥ pivotalRightVector p = response • pivotalRightVector p) :
    M.charpoly = (X - C response) *
      (X ^ 2 - C (Matrix.trace (massPlaneBlock M)) * X + C (Matrix.det (massPlaneBlock M))) := by
  have h := criticalBlock_conjugation M p response hp hplane heigen
  have hc := congrArg Matrix.charpoly h
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    criticalBasis_mul_inverse p hp, Matrix.one_mul] at hc
  exact hc.trans (criticalBlock_charpoly M response)

namespace FiniteNetwork

theorem massMatrix_charpoly {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (p : ℝ) (hfixed : R.reliability p = p) (hp : p ≠ 0) (hp' : p ≠ 1)
    (symmetry : R.NetworkSymmetry) (hs : symmetry.vertex R.source = R.target)
    (ht : symmetry.vertex R.target = R.source) :
    (R.massMatrix p).charpoly = (X - C (deriv R.reliability p)) *
      (X ^ 2 - C (Matrix.trace (massPlaneBlock (R.massMatrix p))) * X +
        C (Matrix.det (massPlaneBlock (R.massMatrix p)))) := by
  exact critical_charpoly _ p _ hp (R.massMatrix_preservesMassPlane p symmetry hs ht)
    (R.pivotal_right_eigenvector_at_fixed_point p hfixed hp hp' symmetry hs ht)

theorem massPlaneBlock_trace_mem_adjoin {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) :
    Matrix.trace (massPlaneBlock (R.massMatrix p)) ∈ IntermediateField.adjoin ℚ {p} := by
  apply (IntermediateField.adjoin ℚ {p}).sum_mem
  intro i _
  exact R.massPlaneBlock_mem_adjoin p i i

theorem massPlaneBlock_det_mem_adjoin {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) :
    Matrix.det (massPlaneBlock (R.massMatrix p)) ∈ IntermediateField.adjoin ℚ {p} := by
  rw [Matrix.det_fin_two]
  exact (IntermediateField.adjoin ℚ {p}).sub_mem
    ((IntermediateField.adjoin ℚ {p}).mul_mem (R.massPlaneBlock_mem_adjoin p 0 0)
      (R.massPlaneBlock_mem_adjoin p 1 1))
    ((IntermediateField.adjoin ℚ {p}).mul_mem (R.massPlaneBlock_mem_adjoin p 0 1)
      (R.massPlaneBlock_mem_adjoin p 1 0))

end FiniteNetwork
end
end Universality
