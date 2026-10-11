import Universality.Matrix.TwoByTwoExpansion
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

namespace Universality
noncomputable section
open Matrix

def perronProjection (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (positiveRoot A - secondaryRoot A)⁻¹ • (A - secondaryRoot A • 1)

theorem secondaryRoot_abs_lt (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    |secondaryRoot A| < positiveRoot A := by
  have hdisc : 0 < (A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0 := by
    nlinarith [mul_pos (hA 0 1) (hA 1 0), sq_nonneg (A 0 0 - A 1 1)]
  have hsqrt := Real.sqrt_pos.mpr hdisc
  rw [abs_lt]
  unfold secondaryRoot positiveRoot
  rw [Matrix.trace_fin_two]
  constructor <;> linarith [hA 0 0, hA 1 1]

theorem perron_gap_pos (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    0 < positiveRoot A - secondaryRoot A :=
  sub_pos.mpr ((le_abs_self _).trans_lt (secondaryRoot_abs_lt A hA))

theorem positiveRoot_mul_secondaryRoot (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : positiveRoot A * secondaryRoot A = A.det := by
  have h := positiveRoot_quadratic A hA
  unfold secondaryRoot
  nlinarith

theorem twoByTwo_root_identity (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    A * A = (positiveRoot A + secondaryRoot A) • A -
      (positiveRoot A * secondaryRoot A) • 1 := by
  rw [positiveRoot_mul_secondaryRoot A hA]
  have hsum : positiveRoot A + secondaryRoot A = A.trace := by unfold secondaryRoot; ring
  rw [hsum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem mul_perronProjection (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    A * perronProjection A = positiveRoot A • perronProjection A := by
  unfold perronProjection
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    twoByTwo_root_identity A hA]
  module

theorem perronProjection_decomposition (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    A = positiveRoot A • perronProjection A + secondaryRoot A • (1 - perronProjection A) := by
  have hgap := (perron_gap_pos A hA).ne'
  unfold perronProjection
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem mul_complement_perronProjection (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    A * (1 - perronProjection A) = secondaryRoot A • (1 - perronProjection A) := by
  rw [Matrix.mul_sub, Matrix.mul_one, mul_perronProjection A hA]
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using perronProjection_decomposition A hA)

/-- Exact spectral decomposition of every power of a positive two-by-two matrix. -/
theorem positive_matrix_power_decomposition (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (n : ℕ) :
    A ^ n = positiveRoot A ^ n • perronProjection A +
      secondaryRoot A ^ n • (1 - perronProjection A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      mul_perronProjection A hA, mul_complement_perronProjection A hA]
    simp only [smul_smul, pow_succ]

theorem perronProjection_pos (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    ∀ i j, 0 < perronProjection A i j := by
  have hfirst := positiveRoot_sub_diagonal_pos A hA
  have hother : 0 < positiveRoot A - A 1 1 := by
    have hroot := positiveRoot_quadratic A hA
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hroot
    have hprod : 0 < (positiveRoot A - A 0 0) * (positiveRoot A - A 1 1) := by
      nlinarith [mul_pos (hA 0 1) (hA 1 0)]
    exact pos_of_mul_pos_right hprod hfirst.le
  intro i j
  unfold perronProjection
  apply mul_pos (inv_pos.mpr (perron_gap_pos A hA))
  fin_cases i <;> fin_cases j <;>
    simp [secondaryRoot, Matrix.trace_fin_two] <;>
    linarith [hA 0 1, hA 1 0]

end
end Universality
