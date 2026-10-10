import Universality.Matrix.PositiveTwoByTwo

namespace Universality
noncomputable section
open Matrix

/-- A positive test vector bounds the genuine Perron root from above. -/
theorem positiveRoot_lt_of_test_ratio (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (ratio bound : ℝ) (hratio : 0 < ratio)
    (hfirst : A 0 0 + A 0 1 * ratio < bound)
    (hlast : A 1 0 + A 1 1 * ratio < bound * ratio) : positiveRoot A < bound := by
  have hgap := positiveRoot_sub_diagonal_pos A hA
  have hweight : 0 < A 1 0 + (positiveRoot A - A 0 0) * ratio :=
    add_pos (hA 1 0) (mul_pos hgap hratio)
  have hquad := positiveRoot_quadratic A hA
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hquad
  have hid : A 1 0 * (A 0 0 + A 0 1 * ratio) +
      (positiveRoot A - A 0 0) * (A 1 0 + A 1 1 * ratio) =
      positiveRoot A * (A 1 0 + (positiveRoot A - A 0 0) * ratio) := by
    nlinarith [congrArg (fun value : ℝ => value * ratio) hquad]
  have hbound : positiveRoot A * (A 1 0 + (positiveRoot A - A 0 0) * ratio) <
      bound * (A 1 0 + (positiveRoot A - A 0 0) * ratio) := by
    rw [← hid]
    nlinarith [mul_lt_mul_of_pos_left hfirst (hA 1 0),
      mul_lt_mul_of_pos_left hlast hgap]
  exact (mul_lt_mul_iff_left₀ hweight).mp hbound

/-- A positive test vector bounds the genuine Perron root from below. -/
theorem lt_positiveRoot_of_test_ratio (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (ratio bound : ℝ) (hratio : 0 < ratio)
    (hfirst : bound < A 0 0 + A 0 1 * ratio)
    (hlast : bound * ratio < A 1 0 + A 1 1 * ratio) : bound < positiveRoot A := by
  have hgap := positiveRoot_sub_diagonal_pos A hA
  have hweight : 0 < A 1 0 + (positiveRoot A - A 0 0) * ratio :=
    add_pos (hA 1 0) (mul_pos hgap hratio)
  have hquad := positiveRoot_quadratic A hA
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hquad
  have hid : A 1 0 * (A 0 0 + A 0 1 * ratio) +
      (positiveRoot A - A 0 0) * (A 1 0 + A 1 1 * ratio) =
      positiveRoot A * (A 1 0 + (positiveRoot A - A 0 0) * ratio) := by
    nlinarith [congrArg (fun value : ℝ => value * ratio) hquad]
  have hbound : bound * (A 1 0 + (positiveRoot A - A 0 0) * ratio) <
      positiveRoot A * (A 1 0 + (positiveRoot A - A 0 0) * ratio) := by
    rw [← hid]
    nlinarith [mul_lt_mul_of_pos_left hfirst (hA 1 0),
      mul_lt_mul_of_pos_left hlast hgap]
  exact (mul_lt_mul_iff_left₀ hweight).mp hbound

end
end Universality
