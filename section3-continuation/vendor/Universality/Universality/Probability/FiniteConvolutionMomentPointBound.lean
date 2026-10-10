import Universality.Probability.FiniteConvolutionPointBounds

namespace Universality
noncomputable section

theorem finite_convolution_first_moment_le {first second : Type*}
    [Fintype first] [Fintype second]
    (firstWeight : first → ℝ) (secondWeight : second → ℝ)
    (firstMass : first → ℕ) (secondMass : second → ℕ)
    (hfirst : ∀ i, 0 ≤ firstWeight i) (hsecond : ∀ j, 0 ≤ secondWeight j)
    (hsecondNormalized : ∑ j, secondWeight j = 1) (order : ℕ) :
    (∑ i, firstWeight i * (firstMass i : ℝ) ^ order) ≤
      ∑ i, ∑ j, firstWeight i * secondWeight j * ((firstMass i + secondMass j : ℕ) : ℝ) ^ order := by
  have heq : (∑ i, firstWeight i * (firstMass i : ℝ) ^ order) =
      ∑ i, ∑ j, firstWeight i * secondWeight j * (firstMass i : ℝ) ^ order := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = firstWeight i * (∑ j, secondWeight j) * (firstMass i : ℝ) ^ order := by rw [hsecondNormalized, mul_one]
      _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
  rw [heq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hfirst i) (hsecond j))
  apply pow_le_pow_left₀ (Nat.cast_nonneg _) _
  exact_mod_cast Nat.le_add_right (firstMass i) (secondMass j)

theorem finite_convolution_point_bound_by_moment {first second : Type*}
    [Fintype first] [Fintype second]
    (firstWeight : first → ℝ) (secondWeight : second → ℝ)
    (firstMass : first → ℕ) (secondMass : second → ℕ)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hfirst : ∀ i, 0 ≤ firstWeight i) (hsecond : ∀ j, 0 ≤ secondWeight j)
    (hfirstNormalized : ∑ i, firstWeight i = 1) (hsecondNormalized : ∑ j, secondWeight j = 1)
    (hfirstPoint : ∀ size : ℕ, (∑ i, if firstMass i = size then firstWeight i else 0) ≤ bound)
    (hsecondPoint : ∀ size : ℕ, (∑ j, if secondMass j = size then secondWeight j else 0) ≤ bound)
    (order size : ℕ) :
    (size : ℝ) ^ order * (∑ i, ∑ j, if firstMass i + secondMass j = size
      then firstWeight i * secondWeight j else 0) ≤
      2 ^ (order + 1) * bound *
        (∑ i, ∑ j, firstWeight i * secondWeight j * ((firstMass i + secondMass j : ℕ) : ℝ) ^ order) := by
  have hfirstMoment := finite_convolution_first_moment_le firstWeight secondWeight firstMass secondMass
    hfirst hsecond hsecondNormalized order
  have hsecondMoment := finite_convolution_first_moment_le secondWeight firstWeight secondMass firstMass
    hsecond hfirst hfirstNormalized order
  rw [Finset.sum_comm] at hsecondMoment
  simp only [Nat.add_comm, mul_comm (secondWeight _) (firstWeight _)] at hsecondMoment
  have hmomentNonnegative : 0 ≤ ∑ i, ∑ j,
      firstWeight i * secondWeight j * ((firstMass i + secondMass j : ℕ) : ℝ) ^ order := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (hfirst i) (hsecond j)) (pow_nonneg (Nat.cast_nonneg _) _)
  have hpower : (2 : ℝ) ^ (order - 1) ≤ 2 ^ order :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  apply (finite_convolution_power_point_bound firstWeight secondWeight firstMass secondMass bound bound
    hfirst hsecond hfirstPoint hsecondPoint order size).trans
  calc
    _ ≤ 2 ^ (order - 1) * (2 * bound * (∑ i, ∑ j,
        firstWeight i * secondWeight j * ((firstMass i + secondMass j : ℕ) : ℝ) ^ order)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      nlinarith [mul_le_mul_of_nonneg_left hfirstMoment hbound,
        mul_le_mul_of_nonneg_left hsecondMoment hbound]
    _ ≤ 2 ^ order * (2 * bound * (∑ i, ∑ j,
        firstWeight i * secondWeight j * ((firstMass i + secondMass j : ℕ) : ℝ) ^ order)) :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = _ := by rw [pow_succ]; ring

end
end Universality
