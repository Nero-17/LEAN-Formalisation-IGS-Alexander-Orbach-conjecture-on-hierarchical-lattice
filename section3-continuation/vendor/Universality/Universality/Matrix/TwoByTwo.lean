import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit two by two matrix calculations for hierarchical percolation

The matrices are genuine `Matrix (Fin 2) (Fin 2)` objects.  No spectral or
percolation conclusions are included in a numerical identity by definition.
-/

namespace Universality

def wheatstoneBlock : Matrix (Fin 2) (Fin 2) ℚ :=
  !![53 / 16, 48 / 16; 13 / 16, 42 / 16]

def oppositeWheatstoneBlock : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1896 / 256, 2292 / 256; 627 / 256, 1380 / 256]

theorem noncommutative_trace_difference :
    Matrix.trace (wheatstoneBlock ^ 2 * oppositeWheatstoneBlock ^ 2) -
      Matrix.trace (wheatstoneBlock * oppositeWheatstoneBlock *
        wheatstoneBlock * oppositeWheatstoneBlock) = -1521 / 4194304 := by
  norm_num [wheatstoneBlock, oppositeWheatstoneBlock, pow_two,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

theorem noncommutative_determinants_eq :
    Matrix.det (wheatstoneBlock ^ 2 * oppositeWheatstoneBlock ^ 2) =
      Matrix.det (wheatstoneBlock * oppositeWheatstoneBlock *
        wheatstoneBlock * oppositeWheatstoneBlock) := by
  simp only [pow_two, Matrix.det_mul]
  ring

theorem noncommutative_determinant_ne_zero :
    Matrix.det (wheatstoneBlock ^ 2 * oppositeWheatstoneBlock ^ 2) ≠ 0 := by
  norm_num [pow_two, Matrix.det_mul, Matrix.det_fin_two, wheatstoneBlock,
    oppositeWheatstoneBlock]

theorem noncommutative_traces_ne :
    Matrix.trace (wheatstoneBlock ^ 2 * oppositeWheatstoneBlock ^ 2) ≠
      Matrix.trace (wheatstoneBlock * oppositeWheatstoneBlock *
        wheatstoneBlock * oppositeWheatstoneBlock) := by
  intro h
  have hd := noncommutative_trace_difference
  rw [h, sub_self] at hd
  norm_num at hd

/-- Equal nonzero roots and equal constant coefficients force equal linear
coefficients.  This is the algebraic step used to distinguish the Perron roots.
It does not postulate their existence or their spectral interpretation. -/
theorem quadratic_trace_eq_of_common_nonzero_root {K : Type*} [Field K]
    {trace₁ trace₂ determinant root : K} (hroot : root ≠ 0)
    (h₁ : root ^ 2 - trace₁ * root + determinant = 0)
    (h₂ : root ^ 2 - trace₂ * root + determinant = 0) : trace₁ = trace₂ := by
  have h : (trace₁ - trace₂) * root = 0 := by
    calc
      (trace₁ - trace₂) * root =
          (root ^ 2 - trace₂ * root + determinant) -
            (root ^ 2 - trace₁ * root + determinant) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hroot)

end Universality
