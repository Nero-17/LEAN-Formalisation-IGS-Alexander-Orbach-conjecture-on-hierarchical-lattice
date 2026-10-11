import Universality.Matrix.PopulationGrowth

namespace Universality
noncomputable section
open Matrix
set_option maxHeartbeats 0

theorem matrix_row_sum_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (bound : ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hbound : 0 ≤ bound) (hrows : ∀ i, ∑ j, M i j ≤ bound) (n : ℕ) :
    ∀ i, ∑ j, (M ^ n) i j ≤ bound ^ n := by
  induction n with
  | zero => intro i; simp [Matrix.one_apply]
  | succ n ih =>
    intro i
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc
      _ ≤ ∑ k, (M ^ n) i k * bound := Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hrows k) (matrix_pow_nonneg M hM n i k))
      _ = (∑ k, (M ^ n) i k) * bound := (Finset.sum_mul ..).symm
      _ ≤ bound ^ n * bound := mul_le_mul_of_nonneg_right (ih i) hbound

/-- A positive power propagates a strict row deficit to every row. -/
theorem matrix_row_sum_power_strict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (bound : ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hbound : 0 ≤ bound) (hrows : ∀ i, ∑ j, M i j ≤ bound)
    (strictRow : ι) (hstrict : ∑ j, M strictRow j < bound)
    (n : ℕ) (hpositive : ∀ i j, 0 < (M ^ n) i j) :
    ∀ i, ∑ j, (M ^ (n + 1)) i j < bound ^ (n + 1) := by
  intro i
  simp only [pow_succ, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    _ < ∑ k, (M ^ n) i k * bound := by
      apply Finset.sum_lt_sum
      · intro k _
        exact mul_le_mul_of_nonneg_left (hrows k) (hpositive i k).le
      · exact ⟨strictRow, Finset.mem_univ _, mul_lt_mul_of_pos_left hstrict (hpositive i strictRow)⟩
    _ = (∑ k, (M ^ n) i k) * bound := (Finset.sum_mul ..).symm
    _ ≤ bound ^ n * bound := mul_le_mul_of_nonneg_right
      (matrix_row_sum_pow_le M bound hM hbound hrows n i) hbound

theorem positive_eigenvalue_lt_of_strict_row_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (radius bound : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i)
    (hr : 0 ≤ radius) (hb : 0 ≤ bound)
    (heigen : M *ᵥ weight = radius • weight)
    (hrows : ∀ i, ∑ j, M i j ≤ bound)
    (strictRow : ι) (hstrict : ∑ j, M strictRow j < bound)
    (n : ℕ) (hpositive : ∀ i j, 0 < (M ^ n) i j) : radius < bound := by
  classical
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  have heq := congrFun (common_eigenvector_pow M weight radius heigen (n + 1)) imax
  change (∑ j, (M ^ (n + 1)) imax j * weight j) = radius ^ (n + 1) * weight imax at heq
  have hpower : radius ^ (n + 1) < bound ^ (n + 1) := by
    apply (mul_lt_mul_iff_left₀ (hw imax)).mp
    calc
      _ = ∑ j, (M ^ (n + 1)) imax j * weight j := heq.symm
      _ ≤ ∑ j, (M ^ (n + 1)) imax j * weight imax := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ _))
          (matrix_pow_nonneg M hM (n + 1) imax j))
      _ = (∑ j, (M ^ (n + 1)) imax j) * weight imax := (Finset.sum_mul ..).symm
      _ < bound ^ (n + 1) * weight imax := mul_lt_mul_of_pos_right
        (matrix_row_sum_power_strict M bound hM hb hrows strictRow hstrict n hpositive imax) (hw imax)
  by_contra h
  exact (not_lt_of_ge (pow_le_pow_left₀ hb (le_of_not_gt h) _)) hpower

end
end Universality
