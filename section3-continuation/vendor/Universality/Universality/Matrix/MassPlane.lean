import Universality.Percolation.WheatstoneKernels
import Universality.Matrix.PositiveTwoByTwo

/-!
# The invariant plane of the three-state mass recursion

The two-dimensional block is a restriction of the full operator.  Its positive
eigenvector lifts to a positive three-state vector, identifying the full
spectral radius without discarding the third state.
-/

namespace Universality
noncomputable section
open Matrix FiniteNetwork

theorem sum_liveState {α : Type*} [AddCommMonoid α] (f : LiveState → α) :
    ∑ σ, f σ = f .connected + f .both + f .single := by
  have h : (Finset.univ : Finset LiveState) = {.connected, .both, .single} := by decide
  rw [h]
  simp [add_assoc]

def massPlaneLift (v : Fin 2 → ℝ) : LiveState → ℝ
  | .connected => v 0
  | .both => 2 * v 1
  | .single => v 1

def massPlaneBlock (M : Matrix LiveState LiveState ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![M .connected .connected, 2 * M .connected .both + M .connected .single;
     M .single .connected, 2 * M .single .both + M .single .single]

def PreservesMassPlane (M : Matrix LiveState LiveState ℝ) : Prop :=
  ∀ v, M *ᵥ massPlaneLift v = massPlaneLift (massPlaneBlock M *ᵥ v)

theorem preservesMassPlane_of_entries (M : Matrix LiveState LiveState ℝ)
    (hfirst : M .both .connected = 2 * M .single .connected)
    (hsecond : 2 * M .both .both + M .both .single =
      2 * (2 * M .single .both + M .single .single)) : PreservesMassPlane M := by
  intro v
  ext σ
  cases σ <;> simp [Matrix.mulVec, dotProduct, sum_liveState, massPlaneLift,
    massPlaneBlock, Fin.sum_univ_two] <;>
    nlinarith [congrArg (fun a : ℝ => a * v 0) hfirst,
      congrArg (fun a : ℝ => a * v 1) hsecond]

theorem massPlaneLift_smul (a : ℝ) (v : Fin 2 → ℝ) :
    massPlaneLift (a • v) = a • massPlaneLift v := by
  ext σ
  cases σ <;> simp [massPlaneLift, mul_left_comm]

def massPlaneProject (w : LiveState → ℝ) : Fin 2 → ℝ := ![w .connected, w .single]

theorem massPlaneProject_lift (v : Fin 2 → ℝ) :
    massPlaneProject (massPlaneLift v) = v := by
  ext i
  fin_cases i <;> rfl

theorem massPlaneBlock_mulVec (M : Matrix LiveState LiveState ℝ) (v : Fin 2 → ℝ) :
    massPlaneBlock M *ᵥ v = massPlaneProject (M *ᵥ massPlaneLift v) := by
  ext i
  fin_cases i <;> simp [massPlaneBlock, massPlaneProject, Matrix.mulVec, dotProduct,
    sum_liveState, massPlaneLift, Fin.sum_univ_two] <;> ring

theorem massPlaneBlock_mul (A B : Matrix LiveState LiveState ℝ)
    (hB : PreservesMassPlane B) :
    massPlaneBlock (A * B) = massPlaneBlock A * massPlaneBlock B := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [massPlaneBlock_mulVec, ← Matrix.mulVec_mulVec, hB,
    ← massPlaneBlock_mulVec, Matrix.mulVec_mulVec]

theorem PreservesMassPlane.mul {A B : Matrix LiveState LiveState ℝ}
    (hA : PreservesMassPlane A) (hB : PreservesMassPlane B) :
    PreservesMassPlane (A * B) := by
  intro v
  rw [← Matrix.mulVec_mulVec, hB, hA, massPlaneBlock_mul A B hB,
    ← Matrix.mulVec_mulVec]

theorem preservesMassPlane_one : PreservesMassPlane 1 := by
  have hbc : LiveState.both ≠ .connected := by decide
  have huc : LiveState.single ≠ .connected := by decide
  have hbu : LiveState.both ≠ .single := by decide
  apply preservesMassPlane_of_entries <;>
    norm_num [Matrix.one_apply, hbc, huc, hbu, Ne.symm hbu]

theorem PreservesMassPlane.pow {A : Matrix LiveState LiveState ℝ}
    (hA : PreservesMassPlane A) (n : ℕ) : PreservesMassPlane (A ^ n) := by
  induction n with
  | zero => simpa using preservesMassPlane_one
  | succ n ih => simpa only [pow_succ] using ih.mul hA

theorem massPlaneBlock_one : massPlaneBlock 1 = 1 := by
  have hcb : LiveState.connected ≠ .both := by decide
  have hcu : LiveState.connected ≠ .single := by decide
  have hub : LiveState.single ≠ .both := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [massPlaneBlock, Matrix.one_apply, hcb, hcu, hub, Ne.symm hcu]

theorem massPlaneBlock_pow (A : Matrix LiveState LiveState ℝ)
    (hA : PreservesMassPlane A) (n : ℕ) :
    massPlaneBlock (A ^ n) = massPlaneBlock A ^ n := by
  induction n with
  | zero => simpa using massPlaneBlock_one
  | succ n ih => rw [pow_succ, massPlaneBlock_mul _ _ hA, ih, pow_succ]

theorem massPlaneLift_pos (v : Fin 2 → ℝ) (hv : ∀ i, 0 < v i) :
    ∀ σ, 0 < massPlaneLift v σ := by
  intro σ
  cases σ
  · exact hv 0
  · exact mul_pos (by norm_num) (hv 1)
  · exact hv 1

theorem massPlane_spectralRadius (M : Matrix LiveState LiveState ℝ)
    (hM : ∀ σ τ, 0 ≤ M σ τ) (hplane : PreservesMassPlane M)
    (hblock : ∀ i j, 0 < massPlaneBlock M i j) :
    spectralRadius ℂ (M.map Complex.ofReal) =
      ENNReal.ofReal (positiveRoot (massPlaneBlock M)) := by
  apply spectralRadius_eq_of_positive_eigenvector M
    (massPlaneLift ![massPlaneBlock M 0 1,
      positiveRoot (massPlaneBlock M) - massPlaneBlock M 0 0])
    (positiveRoot (massPlaneBlock M))
  · exact hM
  · apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  · exact (positiveRoot_pos _ hblock).le
  · rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul]

theorem outerPairKernel_preservesMassPlane :
    PreservesMassPlane ((Rat.castHom ℝ).mapMatrix outerPairKernel) := by
  apply preservesMassPlane_of_entries <;>
    norm_num [outerPairKernel, outerPairKernelCount, RingHom.mapMatrix_apply,
      Matrix.map_apply]

theorem centralKernel_preservesMassPlane :
    PreservesMassPlane ((Rat.castHom ℝ).mapMatrix centralKernel) := by
  apply preservesMassPlane_of_entries <;>
    norm_num [centralKernel, centralKernelCount, RingHom.mapMatrix_apply,
      Matrix.map_apply]

end
end Universality
