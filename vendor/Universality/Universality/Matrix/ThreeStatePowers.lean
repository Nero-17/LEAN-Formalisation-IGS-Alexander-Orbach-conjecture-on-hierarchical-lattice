import Universality.Matrix.CriticalBlockDecomposition

namespace Universality
noncomputable section
open Matrix FiniteNetwork

/-- The block power in the conjugation formula is exactly the power of the
two-dimensional block together with the scalar response power. -/
theorem criticalBlock_pow (M : Matrix LiveState LiveState ℝ) (response : ℝ) (n : ℕ) :
    criticalBlock M response ^ n = fun σ τ => match σ, τ with
      | .connected, .connected => (massPlaneBlock M ^ n) 0 0
      | .connected, .both => (massPlaneBlock M ^ n) 0 1
      | .both, .connected => (massPlaneBlock M ^ n) 1 0
      | .both, .both => (massPlaneBlock M ^ n) 1 1
      | .single, .single => response ^ n
      | _, _ => 0 := by
  induction n with
  | zero =>
    ext σ τ
    cases σ <;> cases τ <;> norm_num [Matrix.one_apply] <;> decide
  | succ n ih =>
    rw [pow_succ, ih]
    ext σ τ
    cases σ <;> cases τ <;>
      simp [criticalBlock, Matrix.mul_apply, sum_liveState, pow_succ, Fin.sum_univ_two]

end
end Universality
