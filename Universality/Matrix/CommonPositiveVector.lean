import Universality.Matrix.PositiveEigenvector

/-!
# Products sharing a strictly positive eigenvector

This is the mechanism behind the infinite family in Section 5.  It explains why
spectral radii multiply for those particular matrices, although they need not
multiply for arbitrary substitutions.
-/

namespace Universality
open Matrix

theorem common_eigenvector_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (weight : ι → ℝ) (a b : ℝ)
    (hA : A *ᵥ weight = a • weight) (hB : B *ᵥ weight = b • weight) :
    (A * B) *ᵥ weight = (a * b) • weight := by
  rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul, hA, smul_smul, mul_comm b a]

theorem common_positive_vector_spectralRadius_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℝ) (weight : ι → ℝ) (a b : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hw : ∀ i, 0 < weight i) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAv : A *ᵥ weight = a • weight) (hBv : B *ᵥ weight = b • weight) :
    spectralRadius ℂ ((A * B).map Complex.ofReal) = ENNReal.ofReal (a * b) := by
  apply spectralRadius_eq_of_positive_eigenvector (A * B) weight (a * b)
  · intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))
  · exact hw
  · exact mul_nonneg ha hb
  · exact common_eigenvector_mul A B weight a b hAv hBv

theorem common_eigenvector_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (weight : ι → ℝ) (a : ℝ)
    (hA : A *ᵥ weight = a • weight) (n : ℕ) :
    (A ^ n) *ᵥ weight = (a ^ n) • weight := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa only [pow_succ] using common_eigenvector_mul (A ^ n) A weight
        (a ^ n) a ih hA

end Universality
