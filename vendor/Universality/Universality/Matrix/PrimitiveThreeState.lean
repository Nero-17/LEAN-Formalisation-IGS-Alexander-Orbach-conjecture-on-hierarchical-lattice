import Universality.Matrix.PopulationGrowth
import Universality.Percolation.FiniteNetwork

namespace Universality
noncomputable section
open Matrix FiniteNetwork

theorem matrix_mul_entry_pos {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (i k j : ι) (ha : 0 < A i k) (hb : 0 < B k j) : 0 < (A * B) i j := by
  rw [Matrix.mul_apply]
  apply (Finset.sum_pos_iff_of_nonneg (fun x _ => mul_nonneg (hA i x) (hB x j))).mpr
  exact ⟨k, Finset.mem_univ k, mul_pos ha hb⟩

theorem matrix_power_four_pos_of_path {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (a b c d e : ι) (hab : 0 < M a b) (hbc : 0 < M b c)
    (hcd : 0 < M c d) (hde : 0 < M d e) : 0 < (M ^ 4) a e := by
  have htwo : 0 < (M ^ 2) a c := by
    rw [pow_two]
    exact matrix_mul_entry_pos M M hM hM a b c hab hbc
  have hthree : 0 < (M ^ 3) a d := by
    change 0 < (M ^ (2 + 1)) a d
    rw [pow_succ]
    exact matrix_mul_entry_pos (M ^ 2) M (matrix_pow_nonneg M hM 2) hM a c d htwo hcd
  change 0 < (M ^ (3 + 1)) a e
  rw [pow_succ]
  exact matrix_mul_entry_pos (M ^ 3) M (matrix_pow_nonneg M hM 3) hM a d e hthree hde

/-- The three-state cycle and the connected-state loop give the explicit
primitivity exponent four. -/
theorem three_state_fourth_power_pos (M : Matrix LiveState LiveState ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hcc : 0 < M .connected .connected) (hcb : 0 < M .connected .both)
    (hbu : 0 < M .both .single) (huc : 0 < M .single .connected) :
    ∀ i j, 0 < (M ^ 4) i j := by
  intro i j
  cases i <;> cases j
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ hcc hcc hcc hcc
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ hcc hcc hcc hcb
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ hcc hcc hcb hbu
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ hbu huc hcc hcc
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ hbu huc hcc hcb
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ hbu huc hcb hbu
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ huc hcc hcc hcc
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ huc hcc hcc hcb
  · exact matrix_power_four_pos_of_path M hM _ _ _ _ _ huc hcc hcb hbu

end
end Universality
