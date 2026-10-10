import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

/-! Algebraic closure arguments used for the actual graph response matrices. -/

namespace Universality.Section4
noncomputable section
open Polynomial Matrix

theorem polynomial_eval_mem_field (field : IntermediateField ℚ ℝ)
    {p : ℝ} (hp : p ∈ field) (polynomial : Polynomial ℚ) :
    polynomial.eval₂ (Rat.castHom ℝ) p ∈ field := by
  induction polynomial using Polynomial.induction_on' with
  | add polynomial₁ polynomial₂ h₁ h₂ =>
      simpa only [Polynomial.eval₂_add] using field.add_mem h₁ h₂
  | monomial degree coefficient =>
      rw [Polynomial.eval₂_monomial]
      exact field.mul_mem (SubfieldClass.ratCast_mem field coefficient)
        (field.toSubalgebra.pow_mem hp degree)

theorem isAlgebraic_matrix_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℂ) (halgebraic : ∀ i j, IsAlgebraic ℚ (matrix i j))
    {eigenvalue : ℂ} (heigenvalue : eigenvalue ∈ spectrum ℂ matrix) :
    IsAlgebraic ℚ eigenvalue := by
  letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  let algebraicMatrix : Matrix ι ι (algebraicClosure ℚ ℂ) :=
    fun i j => ⟨matrix i j, mem_algebraicClosure_iff.mpr (halgebraic i j)⟩
  have hmap : algebraicMatrix.map (algebraMap (algebraicClosure ℚ ℂ) ℂ) = matrix := rfl
  have hroot : aeval eigenvalue algebraicMatrix.charpoly = 0 := by
    change algebraicMatrix.charpoly.eval₂ (algebraMap (algebraicClosure ℚ ℂ) ℂ) eigenvalue = 0
    rw [← Polynomial.eval_map, ← Matrix.charpoly_map, hmap]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp heigenvalue
  have halgebraicExtension : IsAlgebraic (algebraicClosure ℚ ℂ) eigenvalue :=
    ⟨algebraicMatrix.charpoly, algebraicMatrix.charpoly_monic.ne_zero, hroot⟩
  exact halgebraicExtension.restrictScalars ℚ

end
end Universality.Section4

#print axioms Universality.Section4.polynomial_eval_mem_field
#print axioms Universality.Section4.isAlgebraic_matrix_spectrum
