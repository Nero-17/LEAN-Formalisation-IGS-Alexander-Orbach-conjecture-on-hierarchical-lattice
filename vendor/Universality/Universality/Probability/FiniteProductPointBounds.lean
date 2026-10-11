import Universality.Probability.FiniteConvolutionPointBounds
import Mathlib.Logic.Equiv.Prod

namespace Universality
noncomputable section

theorem finite_sum_split_index {index M : Type*} [Fintype index] [DecidableEq index]
    [AddCommMonoid M] (value : index → M) (chosen : index) :
    (∑ i, value i) = value chosen + ∑ i : {i // i ≠ chosen}, value i := by
  rw [← Finset.sum_subtype (Finset.univ.erase chosen) (by simp) value]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ chosen)).symm

theorem finite_product_split_index {index M : Type*} [Fintype index] [DecidableEq index]
    [CommMonoid M] (value : index → M) (chosen : index) :
    (∏ i, value i) = value chosen * ∏ i : {i // i ≠ chosen}, value i := by
  rw [← Finset.prod_subtype (Finset.univ.erase chosen) (by simp) value]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ chosen)).symm

theorem finite_product_split_observable {index values : Type*} [Fintype index] [DecidableEq index]
    [Fintype values] (weight : index → values → ℝ) (mass : index → values → ℕ)
    (chosen : index) (response : ℕ → ℝ) :
    (∑ configuration : index → values,
      (∏ i, weight i (configuration i)) * response (∑ i, mass i (configuration i))) =
      ∑ value : values, ∑ rest : {i // i ≠ chosen} → values,
        weight chosen value * (∏ i : {i // i ≠ chosen}, weight i (rest i)) *
          response (mass chosen value + ∑ i : {i // i ≠ chosen}, mass i (rest i)) := by
  classical
  rw [← (Equiv.funSplitAt chosen values).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_congr rfl
  intro rest _
  rw [finite_product_split_index _ chosen, finite_sum_split_index _ chosen]
  have hne (i : {i // i ≠ chosen}) : (i : index) ≠ chosen := i.property
  simp [Equiv.funSplitAt, Equiv.piSplitAt, hne]

theorem finite_product_atom_bound {index values : Type*} [Fintype index] [DecidableEq index]
    [Fintype values] (weight : index → values → ℝ) (mass : index → values → ℕ)
    (hweight : ∀ i value, 0 ≤ weight i value) (hnormalized : ∀ i, ∑ value, weight i value = 1)
    (chosen : index) (bound : ℝ)
    (hpoint : ∀ size : ℕ, (∑ value, if mass chosen value = size then weight chosen value else 0) ≤ bound)
    (shift size : ℕ) :
    (∑ configuration : index → values, if shift + ∑ i, mass i (configuration i) = size
      then (∏ i, weight i (configuration i)) else 0) ≤ bound := by
  classical
  have heq : (∑ configuration : index → values, if shift + ∑ i, mass i (configuration i) = size
      then (∏ i, weight i (configuration i)) else 0) =
      ∑ value : values, ∑ rest : {i // i ≠ chosen} → values,
        if (shift + ∑ i : {i // i ≠ chosen}, mass i (rest i)) + mass chosen value = size
          then weight chosen value * (∏ i : {i // i ≠ chosen}, weight i (rest i)) else 0 := by
    have h := finite_product_split_observable weight mass chosen
      (fun total => if shift + total = size then 1 else 0)
    simpa only [mul_ite, mul_one, mul_zero, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
  rw [heq, Finset.sum_comm]
  calc
    _ = ∑ rest : {i // i ≠ chosen} → values,
        (∏ i : {i // i ≠ chosen}, weight i (rest i)) *
          (∑ value, if (shift + ∑ i : {i // i ≠ chosen}, mass i (rest i)) + mass chosen value = size
            then weight chosen value else 0) := by
      apply Finset.sum_congr rfl
      intro rest _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro value _
      split_ifs <;> ring
    _ ≤ ∑ rest : {i // i ≠ chosen} → values, (∏ i : {i // i ≠ chosen}, weight i (rest i)) * bound := by
      apply Finset.sum_le_sum
      intro rest _
      exact mul_le_mul_of_nonneg_left
        (finite_shift_point_bound _ _ bound (hweight chosen) hpoint _ size)
        (Finset.prod_nonneg (fun i _ => hweight i (rest i)))
    _ = bound := by
      rw [← Finset.sum_mul, ← Fintype.prod_sum]
      simp only [hnormalized, Finset.prod_const_one, one_mul]

end
end Universality
