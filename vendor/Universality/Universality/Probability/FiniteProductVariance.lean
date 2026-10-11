import Universality.Percolation.ProductDisintegration
import Universality.Probability.FiniteWeightSquare

namespace Universality
open scoped BigOperators

theorem finite_product_centered_cross_moment {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight response : ι → Ω → ℝ) (hcentered : ∀ i, ∑ a, weight i a * response i a = 0)
    (i j : ι) (hne : i ≠ j) :
    (∑ outcome : ι → Ω, (∏ k, weight k (outcome k)) *
      response i (outcome i) * response j (outcome j)) = 0 := by
  classical
  have hfactor (outcome : ι → Ω) :
      (∏ k, weight k (outcome k)) * response i (outcome i) * response j (outcome j) =
      ∏ k, weight k (outcome k) * (if k = i then response k (outcome k) else 1) *
        (if k = j then response k (outcome k) else 1) := by
    simp only [Finset.prod_mul_distrib]
    simp
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun k a => weight k a * (if k = i then response k a else 1) *
    (if k = j then response k a else 1))]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [hne] using hcentered i

theorem finite_product_centered_sum_sq {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight response : ι → Ω → ℝ) (hsum : ∀ i, ∑ a, weight i a = 1)
    (hcentered : ∀ i, ∑ a, weight i a * response i a = 0) :
    (∑ outcome : ι → Ω, (∏ k, weight k (outcome k)) * (∑ i, response i (outcome i)) ^ 2) =
      ∑ i, ∑ a, weight i a * response i a ^ 2 := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · simpa only [hsum, Finset.prod_const_one, one_mul] using
      finite_product_local_moment weight (fun a => response i a * response i a) i
  · intro j _ hji
    simpa only [mul_assoc] using finite_product_centered_cross_moment weight response hcentered j i hji
  · simp

theorem finite_weighted_centering {Ω : Type*} [Fintype Ω] (weight response : Ω → ℝ)
    (hsum : ∑ a, weight a = 1) :
    (∑ a, weight a * (response a - ∑ b, weight b * response b)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, sub_self]

theorem finite_weighted_variance {Ω : Type*} [Fintype Ω] (weight response : Ω → ℝ)
    (hsum : ∑ a, weight a = 1) :
    (∑ a, weight a * (response a - ∑ b, weight b * response b) ^ 2) =
      (∑ a, weight a * response a ^ 2) - (∑ a, weight a * response a) ^ 2 := by
  calc
    _ = ∑ a, (weight a * response a ^ 2 - 2 * (weight a * response a) *
        (∑ b, weight b * response b) + weight a * (∑ b, weight b * response b) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, ← Finset.sum_mul, hsum]
      ring

theorem finite_product_variance_le_second_moments {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω] (weight response : ι → Ω → ℝ)
    (hsum : ∀ i, ∑ a, weight i a = 1) :
    (∑ outcome : ι → Ω, (∏ k, weight k (outcome k)) *
      ((∑ i, response i (outcome i)) - ∑ i, ∑ a, weight i a * response i a) ^ 2) ≤
      ∑ i, ∑ a, weight i a * response i a ^ 2 := by
  simp_rw [← Finset.sum_sub_distrib]
  rw [finite_product_centered_sum_sq weight
    (fun i a => response i a - ∑ b, weight i b * response i b) hsum
    (fun i => finite_weighted_centering (weight i) (response i) (hsum i))]
  apply Finset.sum_le_sum
  intro i _
  rw [finite_weighted_variance _ _ (hsum i)]
  exact sub_le_self _ (sq_nonneg _)

end Universality
