import Universality.Probability.L2Characteristic

namespace Universality
noncomputable section

theorem finite_shift_point_bound {index : Type*} [Fintype index]
    (weight : index → ℝ) (mass : index → ℕ) (bound : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpoint : ∀ size : ℕ, (∑ i, if mass i = size then weight i else 0) ≤ bound)
    (shift size : ℕ) :
    (∑ i, if shift + mass i = size then weight i else 0) ≤ bound := by
  apply (Finset.sum_le_sum (g := fun i => if mass i = size - shift then weight i else 0) ?_).trans
    (hpoint (size - shift))
  intro i _
  by_cases heq : shift + mass i = size
  · have hmass : mass i = size - shift := by omega
    simp only [if_pos heq, if_pos hmass, le_refl]
  · rw [if_neg heq]
    split_ifs
    · exact hweight i
    · exact le_rfl

/-- Weighting one summand by any nonnegative local response costs its
expectation times the other summand's maximal atom. -/
theorem finite_convolution_local_weighted_point_bound {first second : Type*}
    [Fintype first] [Fintype second]
    (firstWeight : first → ℝ) (secondWeight : second → ℝ)
    (firstMass : first → ℕ) (secondMass : second → ℕ)
    (response : first → ℝ) (bound : ℝ)
    (hfirst : ∀ i, 0 ≤ firstWeight i) (hsecond : ∀ j, 0 ≤ secondWeight j)
    (hresponse : ∀ i, 0 ≤ response i)
    (hpoint : ∀ size : ℕ, (∑ j, if secondMass j = size then secondWeight j else 0) ≤ bound)
    (size : ℕ) :
    (∑ i, ∑ j, if firstMass i + secondMass j = size
      then firstWeight i * secondWeight j * response i else 0) ≤
      bound * ∑ i, firstWeight i * response i := by
  have heq : (∑ i, ∑ j, if firstMass i + secondMass j = size
        then firstWeight i * secondWeight j * response i else 0) =
      ∑ i, (firstWeight i * response i) *
        (∑ j, if firstMass i + secondMass j = size then secondWeight j else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ i, (firstWeight i * response i) * bound := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (finite_shift_point_bound secondWeight secondMass bound hsecond hpoint (firstMass i) size)
        (mul_nonneg (hfirst i) (hresponse i))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- A power-weighted atom bound for an independent sum, obtained by the
elementary power-of-a-sum inequality without a separate tail-probability step. -/
theorem finite_convolution_power_point_bound {first second : Type*}
    [Fintype first] [Fintype second]
    (firstWeight : first → ℝ) (secondWeight : second → ℝ)
    (firstMass : first → ℕ) (secondMass : second → ℕ)
    (firstBound secondBound : ℝ)
    (hfirst : ∀ i, 0 ≤ firstWeight i) (hsecond : ∀ j, 0 ≤ secondWeight j)
    (hfirstPoint : ∀ size : ℕ, (∑ i, if firstMass i = size then firstWeight i else 0) ≤ firstBound)
    (hsecondPoint : ∀ size : ℕ, (∑ j, if secondMass j = size then secondWeight j else 0) ≤ secondBound)
    (order size : ℕ) :
    (size : ℝ) ^ order * (∑ i, ∑ j, if firstMass i + secondMass j = size
      then firstWeight i * secondWeight j else 0) ≤
      2 ^ (order - 1) *
        (secondBound * (∑ i, firstWeight i * (firstMass i : ℝ) ^ order) +
          firstBound * (∑ j, secondWeight j * (secondMass j : ℝ) ^ order)) := by
  have hpointwise (i : first) (j : second) :
      (size : ℝ) ^ order * (if firstMass i + secondMass j = size then firstWeight i * secondWeight j else 0) ≤
        2 ^ (order - 1) *
          ((if firstMass i + secondMass j = size then firstWeight i * secondWeight j * (firstMass i : ℝ) ^ order else 0) +
           (if firstMass i + secondMass j = size then firstWeight i * secondWeight j * (secondMass j : ℝ) ^ order else 0)) := by
    split_ifs with heq
    · rw [← heq, Nat.cast_add]
      have hpow := add_pow_le (Nat.cast_nonneg (firstMass i) : (0 : ℝ) ≤ firstMass i)
        (Nat.cast_nonneg (secondMass j) : (0 : ℝ) ≤ secondMass j) order
      have hscaled := mul_le_mul_of_nonneg_right hpow (mul_nonneg (hfirst i) (hsecond j))
      nlinarith
    · simp
  have hfirstWeighted := finite_convolution_local_weighted_point_bound firstWeight secondWeight
    firstMass secondMass (fun i => (firstMass i : ℝ) ^ order) secondBound hfirst hsecond
    (fun i => pow_nonneg (Nat.cast_nonneg _) _) hsecondPoint size
  have hsecondWeighted := finite_convolution_local_weighted_point_bound secondWeight firstWeight
    secondMass firstMass (fun j => (secondMass j : ℝ) ^ order) firstBound hsecond hfirst
    (fun j => pow_nonneg (Nat.cast_nonneg _) _) hfirstPoint size
  have hbound := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpointwise i j))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  apply add_le_add hfirstWeighted
  rw [Finset.sum_comm]
  simpa only [Nat.add_comm, mul_comm, mul_left_comm] using hsecondWeighted

end
end Universality
