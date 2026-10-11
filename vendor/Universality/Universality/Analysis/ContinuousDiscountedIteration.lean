import Universality.Analysis.DiscountedIteration
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace Universality
noncomputable section

theorem continuous_discountedIteration {α : Type*} [TopologicalSpace α]
    (map : α → α) (forcing : α → ℝ) (discount bound : ℝ)
    (hmap : Continuous map) (hforcing : Continuous forcing)
    (hd : 0 ≤ discount) (hd' : discount < 1) (hbound : ∀ x, |forcing x| ≤ bound) :
    Continuous (discountedIteration map forcing discount) := by
  unfold discountedIteration
  apply continuous_tsum (u := fun n : ℕ => discount ^ (n + 1) * bound)
  · intro n
    exact continuous_const.mul (hforcing.comp (hmap.iterate n))
  · exact ((summable_geometric_of_lt_one hd hd').comp_injective
      (fun a b (h : a + 1 = b + 1) => Nat.add_right_cancel h)).mul_right bound
  · intro n x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hd _)]
    exact mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hd _)

end
end Universality
