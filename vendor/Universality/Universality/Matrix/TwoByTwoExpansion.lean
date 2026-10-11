import Universality.Matrix.PositiveTwoByTwo

namespace Universality
noncomputable section
open Matrix

def secondaryRoot (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A.trace - positiveRoot A

theorem positiveRoot_sub_second_diagonal_pos (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : 0 < positiveRoot A - A 1 1 := by
  have hquad := positiveRoot_quadratic A hA
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hquad
  have hfirst := positiveRoot_sub_diagonal_pos A hA
  have hprod : (positiveRoot A - A 0 0) * (positiveRoot A - A 1 1) = A 0 1 * A 1 0 := by
    nlinarith
  exact (mul_pos_iff_of_pos_left hfirst).mp (hprod ▸ mul_pos (hA 0 1) (hA 1 0))

theorem secondaryRoot_lt_diagonal (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : secondaryRoot A < A 0 0 := by
  have h := positiveRoot_sub_second_diagonal_pos A hA
  simp only [secondaryRoot, Matrix.trace_fin_two]
  linarith

theorem positiveRoot_sub_secondary_pos (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : 0 < positiveRoot A - secondaryRoot A := by
  linarith [secondaryRoot_lt_diagonal A hA, positiveRoot_sub_diagonal_pos A hA]

theorem abs_secondaryRoot_lt_positiveRoot (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : |secondaryRoot A| < positiveRoot A := by
  apply abs_lt.mpr
  constructor
  · simp only [secondaryRoot, Matrix.trace_fin_two]
    linarith [hA 0 0, hA 1 1]
  · linarith [positiveRoot_sub_secondary_pos A hA]

theorem root_sum (A : Matrix (Fin 2) (Fin 2) ℝ) :
    positiveRoot A + secondaryRoot A = A.trace := by simp [secondaryRoot]

theorem root_product (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    positiveRoot A * secondaryRoot A = A.det := by
  have h := positiveRoot_quadratic A hA
  unfold secondaryRoot
  nlinarith

theorem twoByTwo_quadratic (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply] <;> ring

def firstProjector (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (positiveRoot A - secondaryRoot A)⁻¹ • (A - secondaryRoot A • 1)

def secondProjector (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (positiveRoot A - secondaryRoot A)⁻¹ • (positiveRoot A • 1 - A)

theorem projectors_add (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    firstProjector A + secondProjector A = 1 := by
  have hne := (positiveRoot_sub_secondary_pos A hA).ne'
  ext i j
  simp only [firstProjector, secondProjector, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem firstProjector_eigen (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    A * firstProjector A = positiveRoot A • firstProjector A := by
  have hquad := twoByTwo_quadratic A
  have hsum := root_sum A
  have hprod := root_product A hA
  ext i j
  have hentry := congrFun (congrFun hquad i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul] at hentry
  simp only [firstProjector, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [← hsum, ← hprod] at hentry
  nlinarith [congrArg (fun x : ℝ => (positiveRoot A - secondaryRoot A)⁻¹ * x) hentry]

theorem secondProjector_eigen (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, 0 < A i j) :
    A * secondProjector A = secondaryRoot A • secondProjector A := by
  have hquad := twoByTwo_quadratic A
  have hsum := root_sum A
  have hprod := root_product A hA
  ext i j
  have hentry := congrFun (congrFun hquad i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul] at hentry
  simp only [secondProjector, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [← hsum, ← hprod] at hentry
  nlinarith [congrArg (fun x : ℝ => (positiveRoot A - secondaryRoot A)⁻¹ * x) hentry]

theorem twoByTwo_power_expansion (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (n : ℕ) :
    A ^ n = positiveRoot A ^ n • firstProjector A + secondaryRoot A ^ n • secondProjector A := by
  induction n with
  | zero => simpa only [pow_zero, one_smul] using (projectors_add A hA).symm
  | succ n ih =>
    rw [pow_succ', ih, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      firstProjector_eigen A hA, secondProjector_eigen A hA,
      smul_smul, smul_smul, ← pow_succ, ← pow_succ]

theorem twoByTwo_mass_entry_expansion (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (n : ℕ) :
    (A ^ n) 0 0 =
      ((A 0 0 - secondaryRoot A) / (positiveRoot A - secondaryRoot A)) * positiveRoot A ^ n +
      ((positiveRoot A - A 0 0) / (positiveRoot A - secondaryRoot A)) * secondaryRoot A ^ n := by
  rw [twoByTwo_power_expansion A hA n]
  simp only [Matrix.add_apply, Matrix.smul_apply, firstProjector, secondProjector,
    Matrix.sub_apply, smul_eq_mul, Matrix.one_apply_eq]
  ring

theorem twoByTwo_mass_coefficients_positive (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    0 < (A 0 0 - secondaryRoot A) / (positiveRoot A - secondaryRoot A) ∧
      0 < (positiveRoot A - A 0 0) / (positiveRoot A - secondaryRoot A) :=
  ⟨div_pos (sub_pos.mpr (secondaryRoot_lt_diagonal A hA)) (positiveRoot_sub_secondary_pos A hA),
    div_pos (positiveRoot_sub_diagonal_pos A hA) (positiveRoot_sub_secondary_pos A hA)⟩

end
end Universality
