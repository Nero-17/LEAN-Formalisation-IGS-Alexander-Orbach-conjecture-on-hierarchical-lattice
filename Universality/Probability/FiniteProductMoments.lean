import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Universality.Percolation.FirstMoments
import Mathlib.Data.Nat.Choose.Sum

namespace Universality
noncomputable section
open scoped BigOperators

/-- Exact mixed moments of independent finite kernels, without any
assumption about how a separate outer configuration chooses the kernels. -/
theorem finite_product_mixed_moment {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight response : ι → Ω → ℝ) (powers : ι → ℕ) :
    (∑ outcome : ι → Ω, (∏ j, weight j (outcome j)) *
      ∏ j, response j (outcome j) ^ powers j) =
      ∏ j, ∑ outcome, weight j outcome * response j outcome ^ powers j := by
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j outcome => weight j outcome * response j outcome ^ powers j)).symm

/-- Expansion over assignments of the r factors records the exact order of
each child moment; the constant assignments are precisely the linear terms. -/
theorem finite_product_sum_moment {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight response : ι → Ω → ℝ) (r : ℕ) :
    (∑ outcome : ι → Ω, (∏ j, weight j (outcome j)) *
      (∑ j, response j (outcome j)) ^ r) =
      ∑ assignment : Fin r → ι, ∏ j,
        ∑ outcome, weight j outcome *
          response j outcome ^ Fintype.card {k : Fin r // assignment k = j} := by
  classical
  simp_rw [Fintype.sum_pow]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro assignment _
  have hproduct (outcome : ι → Ω) :
      (∏ k, response (assignment k) (outcome (assignment k))) =
        ∏ j, response j (outcome j) ^ Fintype.card {k : Fin r // assignment k = j} := by
    rw [← Fintype.prod_fiberwise' assignment (fun j => response j (outcome j))]
    simp only [Finset.prod_const, Finset.card_univ]
  simp_rw [hproduct]
  exact finite_product_mixed_moment weight response _

theorem finite_product_reward_sum_moment {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight response : ι → Ω → ℝ) (reward : ℝ) (r : ℕ) :
    (∑ outcome : ι → Ω, (∏ j, weight j (outcome j)) *
      (reward + ∑ j, response j (outcome j)) ^ r) =
      ∑ k ∈ Finset.range (r + 1), reward ^ (r - k) * (r.choose k : ℝ) *
        ∑ assignment : Fin k → ι, ∏ j,
          ∑ outcome, weight j outcome *
            response j outcome ^ Fintype.card {a : Fin k // assignment a = j} := by
  classical
  simp_rw [add_comm reward, add_pow]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => rw [← Finset.mul_sum, ← finite_product_sum_moment weight response k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

theorem fiber_card_lt_of_nonconstant {ι : Type*} [DecidableEq ι]
    {r : ℕ} (assignment : Fin r → ι)
    (h : ¬ ∃ j, assignment = fun _ => j) (j : ι) :
    Fintype.card {k : Fin r // assignment k = j} < r := by
  classical
  rw [Fintype.card_subtype]
  have hproper : (Finset.univ.filter fun k : Fin r => assignment k = j) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    apply h
    refine ⟨j, funext fun k => ?_⟩
    have hk : k ∈ Finset.univ.filter fun k : Fin r => assignment k = j := by rw [heq]; simp
    exact (Finset.mem_filter.mp hk).2
  simpa using Finset.card_lt_card hproper

end
end Universality
