import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen

namespace Universality
open scoped BigOperators

theorem finite_weighted_mean_sq_le {α : Type*} [Fintype α]
    (weight value : α → ℝ) (hnonneg : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1) :
    (∑ a, weight a * value a) ^ 2 ≤ ∑ a, weight a * value a ^ 2 := by
  have hnonnegSum : 0 ≤ ∑ a, weight a * (value a - ∑ b, weight b * value b) ^ 2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hnonneg a) (sq_nonneg _))
  have hexpand : (∑ a, weight a * (value a - ∑ b, weight b * value b) ^ 2) =
      (∑ a, weight a * value a ^ 2) - (∑ a, weight a * value a) ^ 2 := by
    calc
      _ = ∑ a, (weight a * value a ^ 2 -
          2 * (weight a * value a) * (∑ b, weight b * value b) +
          weight a * (∑ b, weight b * value b) ^ 2) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.mul_sum, ← Finset.sum_mul, hsum]
        ring
  linarith

theorem finite_weighted_mean_pow_le {α : Type*} [Fintype α]
    (weight value : α → ℝ) (hnonneg : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1)
    (hvalue : ∀ a, 0 ≤ value a) (order : ℕ) :
    (∑ a, weight a * value a) ^ order ≤ ∑ a, weight a * value a ^ order := by
  simpa only [smul_eq_mul] using (convexOn_pow order).map_sum_le
    (t := Finset.univ) (fun a _ => hnonneg a) hsum (fun a _ => hvalue a)

end Universality
