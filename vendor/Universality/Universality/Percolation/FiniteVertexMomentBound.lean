import Universality.Percolation.ConditionalCompactBounds

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem conditionalVertexMoment_le_vertices_pow {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) (state : LiveState) (order : ℕ) :
    R.conditionalVertexMoment p state order ≤ (vertices : ℝ) ^ order := by
  unfold conditionalVertexMoment conditionalInternalMoment
  calc
    _ ≤ ∑ configuration, R.conditionalCellWeight p (state == .connected) configuration * (vertices : ℝ) ^ order := by
      apply Finset.sum_le_sum
      intro configuration _
      apply mul_le_mul_of_nonneg_left _ (R.conditionalCellWeight_nonneg hp hp' _ _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast ((R.internalSelectedMass_le true (state == LiveState.both) configuration).trans
        (by rw [R.card_interior_vertices]; exact Nat.sub_le _ _))
    _ = _ := by rw [← Finset.sum_mul, R.sum_conditionalCellWeight p hpositive hless, one_mul]


theorem expectedInternalBoundaryMoment_le_vertices_pow {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    R.expectedInternalBoundaryMoment p order ≤ (vertices : ℝ) ^ order := by
  unfold expectedInternalBoundaryMoment
  calc
    _ ≤ ∑ configuration, bernoulliWeight p configuration * (vertices : ℝ) ^ order := by
      apply Finset.sum_le_sum
      intro configuration _
      apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast ((R.internalSelectedMass_le true true configuration).trans
        (by rw [R.card_interior_vertices]; exact Nat.sub_le _ _))
    _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

end
end Universality.FiniteNetwork
