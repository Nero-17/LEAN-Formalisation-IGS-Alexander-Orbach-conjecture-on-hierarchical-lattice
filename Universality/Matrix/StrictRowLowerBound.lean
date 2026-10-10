import Universality.Matrix.StrictRowBound

namespace Universality
noncomputable section
open Matrix
set_option maxHeartbeats 0

theorem matrix_row_sum_pow_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (bound : ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hbound : 0 ≤ bound) (hrows : ∀ i, bound ≤ ∑ j, M i j) (n : ℕ) :
    ∀ i, bound ^ n ≤ ∑ j, (M ^ n) i j := by
  induction n with
  | zero => intro i; simp [Matrix.one_apply]
  | succ n ih =>
    intro i
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc
      _ ≤ (∑ k, (M ^ n) i k) * bound := mul_le_mul_of_nonneg_right (ih i) hbound
      _ = ∑ k, (M ^ n) i k * bound := Finset.sum_mul ..
      _ ≤ _ := Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hrows k) (matrix_pow_nonneg M hM n i k))

theorem matrix_row_sum_power_strict_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (bound : ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hbound : 0 ≤ bound) (hrows : ∀ i, bound ≤ ∑ j, M i j)
    (strictRow : ι) (hstrict : bound < ∑ j, M strictRow j)
    (n : ℕ) (hpositive : ∀ i j, 0 < (M ^ n) i j) :
    ∀ i, bound ^ (n + 1) < ∑ j, (M ^ (n + 1)) i j := by
  intro i
  simp only [pow_succ, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    _ ≤ (∑ k, (M ^ n) i k) * bound := mul_le_mul_of_nonneg_right
      (matrix_row_sum_pow_ge M bound hM hbound hrows n i) hbound
    _ = ∑ k, (M ^ n) i k * bound := Finset.sum_mul ..
    _ < _ := by
      apply Finset.sum_lt_sum
      · intro k _
        exact mul_le_mul_of_nonneg_left (hrows k) (hpositive i k).le
      · exact ⟨strictRow, Finset.mem_univ _, mul_lt_mul_of_pos_left hstrict (hpositive i strictRow)⟩

theorem strict_row_lower_bound_lt_positive_eigenvalue {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (radius bound : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i)
    (hr : 0 ≤ radius) (hb : 0 ≤ bound)
    (heigen : M *ᵥ weight = radius • weight)
    (hrows : ∀ i, bound ≤ ∑ j, M i j)
    (strictRow : ι) (hstrict : bound < ∑ j, M strictRow j)
    (n : ℕ) (hpositive : ∀ i j, 0 < (M ^ n) i j) : bound < radius := by
  classical
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ weight Finset.univ_nonempty
  have heq := congrFun (common_eigenvector_pow M weight radius heigen (n + 1)) imin
  change (∑ j, (M ^ (n + 1)) imin j * weight j) = radius ^ (n + 1) * weight imin at heq
  have hpower : bound ^ (n + 1) < radius ^ (n + 1) := by
    apply (mul_lt_mul_iff_left₀ (hw imin)).mp
    calc
      _ < (∑ j, (M ^ (n + 1)) imin j) * weight imin := mul_lt_mul_of_pos_right
        (matrix_row_sum_power_strict_lower M bound hM hb hrows strictRow hstrict n hpositive imin) (hw imin)
      _ = ∑ j, (M ^ (n + 1)) imin j * weight imin := Finset.sum_mul ..
      _ ≤ ∑ j, (M ^ (n + 1)) imin j * weight j := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ _))
          (matrix_pow_nonneg M hM (n + 1) imin j))
      _ = _ := heq
  by_contra h
  exact (not_lt_of_ge (pow_le_pow_left₀ hr (le_of_not_gt h) _)) hpower

end
end Universality
