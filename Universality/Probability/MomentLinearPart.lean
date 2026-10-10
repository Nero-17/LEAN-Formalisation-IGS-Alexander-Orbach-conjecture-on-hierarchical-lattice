import Universality.Probability.FiniteProductMoments

namespace Universality
noncomputable section
open scoped BigOperators

theorem constant_assignment_moment {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight response : ι → Ω → ℝ) (hnormalized : ∀ j, ∑ outcome, weight j outcome = 1)
    (r : ℕ) (j : ι) :
    (∏ i, ∑ outcome, weight i outcome *
      response i outcome ^ Fintype.card {a : Fin r // (fun _ : Fin r => j) a = i}) =
      ∑ outcome, weight j outcome * response j outcome ^ r := by
  classical
  rw [Finset.prod_eq_single j]
  · simp only [Fintype.card_subtype_true, Fintype.card_fin]
  · intro i _ hne
    simp [Ne.symm hne, hnormalized]
  · simp

/-- A normalized product kernel separates the pure r-th child moments from
mixed products. Every exponent in the remainder is strictly below r. -/
theorem finite_product_sum_moment_linear_part {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight response : ι → Ω → ℝ) (hnormalized : ∀ j, ∑ outcome, weight j outcome = 1)
    (r : ℕ) (hr : 0 < r) :
    (∑ outcome : ι → Ω, (∏ j, weight j (outcome j)) * (∑ j, response j (outcome j)) ^ r) =
      (∑ j, ∑ outcome, weight j outcome * response j outcome ^ r) +
      ∑ assignment ∈ (Finset.univ.filter fun assignment : Fin r → ι =>
        ¬ ∃ j, assignment = fun _ => j),
        ∏ j, ∑ outcome, weight j outcome *
          response j outcome ^ Fintype.card {a : Fin r // assignment a = j} := by
  classical
  rw [finite_product_sum_moment]
  have hconstant : (Finset.univ.filter fun assignment : Fin r → ι => ∃ j, assignment = fun _ => j) =
      Finset.univ.image (fun j : ι => fun _ : Fin r => j) := by
    ext assignment
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    simp only [eq_comm]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun assignment : Fin r → ι => ∃ j, assignment = fun _ => j),
    hconstant]
  congr 1
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    exact constant_assignment_moment weight response hnormalized r j
  · intro i _ j _ heq
    exact congrFun heq ⟨0, hr⟩

end
end Universality
