import Universality.Matrix.PositiveEigenvector
import Universality.Matrix.SpectralSeparation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases

/-!
# The Perron root of a strictly positive two by two matrix

The closed formula is identified with the actual complex spectral radius by a
positive-vector certificate.  It is not merely named "spectral radius".
-/

namespace Universality
noncomputable section
open Matrix

def positiveRoot (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A 0 0 + A 1 1 + Real.sqrt ((A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0)) / 2

theorem positiveRoot_quadratic (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    positiveRoot A ^ 2 - A.trace * positiveRoot A + A.det = 0 := by
  have hbc : 0 < A 0 1 * A 1 0 := mul_pos (hA 0 1) (hA 1 0)
  have hdisc : 0 ≤ (A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0 := by
    nlinarith [sq_nonneg (A 0 0 - A 1 1)]
  have hsqrt := Real.sq_sqrt hdisc
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  unfold positiveRoot
  nlinarith

theorem positiveRoot_sub_diagonal_pos (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : 0 < positiveRoot A - A 0 0 := by
  have hbc : 0 < A 0 1 * A 1 0 := mul_pos (hA 0 1) (hA 1 0)
  have hdisc : 0 ≤ (A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0 := by
    nlinarith [sq_nonneg (A 0 0 - A 1 1)]
  have hsqrt := Real.sq_sqrt hdisc
  have hnonneg := Real.sqrt_nonneg ((A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0)
  have hlarge : A 0 0 - A 1 1 <
      Real.sqrt ((A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0) := by
    nlinarith [sq_nonneg (Real.sqrt ((A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0) -
      (A 0 0 - A 1 1))]
  unfold positiveRoot
  linarith

theorem positiveRoot_pos (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : 0 < positiveRoot A := by
  have := positiveRoot_sub_diagonal_pos A hA
  linarith [hA 0 0]

theorem positiveRoot_eigenvector (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    A *ᵥ ![A 0 1, positiveRoot A - A 0 0] =
      positiveRoot A • ![A 0 1, positiveRoot A - A 0 0] := by
  have hquad := positiveRoot_quadratic A hA
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hquad
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> nlinarith

theorem spectralRadius_positive_twoByTwo (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    spectralRadius ℂ (A.map Complex.ofReal) = ENNReal.ofReal (positiveRoot A) := by
  apply spectralRadius_eq_of_positive_eigenvector A
    ![A 0 1, positiveRoot A - A 0 0] (positiveRoot A)
  · exact fun i j => (hA i j).le
  · intro i
    fin_cases i
    · exact hA 0 1
    · exact positiveRoot_sub_diagonal_pos A hA
  · exact (positiveRoot_pos A hA).le
  · exact positiveRoot_eigenvector A hA

end
end Universality
