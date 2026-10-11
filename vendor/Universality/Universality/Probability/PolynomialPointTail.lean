import Universality.Probability.L2Characteristic

namespace Universality
noncomputable section

theorem finite_atom_power_le_moment {index : Type*} [Fintype index]
    (weight : index → ℝ) (mass : index → ℕ) (hweight : ∀ i, 0 ≤ weight i)
    (order size : ℕ) :
    (size : ℝ) ^ order * (∑ i, if mass i = size then weight i else 0) ≤
      ∑ i, weight i * (mass i : ℝ) ^ order := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with heq
  · rw [heq, mul_comm]
  · simpa only [mul_zero] using mul_nonneg (hweight i) (pow_nonneg (Nat.cast_nonneg (mass i)) order)

theorem polynomial_point_tail_of_two_bounds (scale mass probability atomBound powerBound : ℝ)
    (hscale : 0 < scale) (hmass : 0 ≤ mass) (hprobability : 0 ≤ probability)
    (order : ℕ) (hatom : scale * probability ≤ atomBound)
    (hpower : scale * probability * (mass / scale) ^ order ≤ powerBound) :
    probability ≤ (2 ^ (order - 1) * (atomBound + powerBound)) /
      scale / (1 + mass / scale) ^ order := by
  have hpositive : 0 < (1 + mass / scale) ^ order :=
    pow_pos (by positivity) _
  apply (le_div_iff₀ hpositive).mpr
  apply (le_div_iff₀ hscale).mpr
  have hsum := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (div_nonneg hmass hscale.le) order
  have hscaled := mul_le_mul_of_nonneg_left hsum (mul_nonneg hscale.le hprobability)
  simp only [one_pow] at hscaled
  calc
    _ = scale * probability * (1 + mass / scale) ^ order := by ring
    _ ≤ scale * probability * (2 ^ (order - 1) * (1 + (mass / scale) ^ order)) := hscaled
    _ = 2 ^ (order - 1) * (scale * probability + scale * probability * (mass / scale) ^ order) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hatom hpower) (pow_nonneg (by norm_num) _)

end
end Universality
