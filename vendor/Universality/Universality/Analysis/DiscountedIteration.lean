import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section
open Filter
open scoped Topology

def discountedIteration {α : Type*} (map : α → α) (forcing : α → ℝ)
    (discount : ℝ) (x : α) : ℝ :=
  ∑' n : ℕ, discount ^ (n + 1) * forcing (map^[n] x)

theorem discountedIteration_summable {α : Type*} (map : α → α) (forcing : α → ℝ)
    (discount bound : ℝ) (hd : 0 ≤ discount) (hd' : discount < 1)
    (hbound : ∀ x, |forcing x| ≤ bound) (x : α) :
    Summable (fun n : ℕ => discount ^ (n + 1) * forcing (map^[n] x)) := by
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => discount ^ (n + 1) * bound)
    (((summable_geometric_of_lt_one hd hd').comp_injective
      (fun a b (h : a + 1 = b + 1) => Nat.add_right_cancel h)).mul_right bound)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hd _)]
  exact mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hd _)

theorem discountedIteration_bound {α : Type*} (map : α → α) (forcing : α → ℝ)
    (discount bound : ℝ) (hd : 0 ≤ discount) (hd' : discount < 1)
    (hbound : ∀ x, |forcing x| ≤ bound) (x : α) :
    |discountedIteration map forcing discount x| ≤ discount * bound / (1 - discount) := by
  have hseries : HasSum (fun n : ℕ => discount ^ (n + 1) * bound)
      (discount * bound / (1 - discount)) := by
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hd hd').mul_left (discount * bound)
  rw [discountedIteration, ← Real.norm_eq_abs]
  apply tsum_of_norm_bounded hseries
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hd _)]
  exact mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hd _)

theorem discountedIteration_equation {α : Type*} (map : α → α) (forcing : α → ℝ)
    (discount bound : ℝ) (hd : 0 ≤ discount) (hd' : discount < 1)
    (hbound : ∀ x, |forcing x| ≤ bound) (x : α) :
    discountedIteration map forcing discount x =
      discount * forcing x + discount * discountedIteration map forcing discount (map x) := by
  unfold discountedIteration
  rw [(discountedIteration_summable map forcing discount bound hd hd' hbound x).tsum_eq_zero_add]
  simp only [zero_add, pow_one, Function.iterate_zero, id_eq]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [Function.iterate_succ_apply, pow_succ]
  ring

/-- Bounded solutions of the cluster-number functional equation are unique;
the argument requires only a self-map and a strict discount. -/
theorem discounted_equation_unique {α : Type*} (map : α → α) (forcing first second : α → ℝ)
    (discount firstBound secondBound : ℝ) (hd : 0 ≤ discount) (hd' : discount < 1)
    (hfirstBound : ∀ x, |first x| ≤ firstBound) (hsecondBound : ∀ x, |second x| ≤ secondBound)
    (hfirst : ∀ x, first x = discount * forcing x + discount * first (map x))
    (hsecond : ∀ x, second x = discount * forcing x + discount * second (map x)) :
    first = second := by
  have heq (n : ℕ) (x : α) :
      first x - second x = discount ^ n * (first (map^[n] x) - second (map^[n] x)) := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      calc
        _ = discount * (first (map x) - second (map x)) := by rw [hfirst x, hsecond x]; ring
        _ = _ := by rw [ih (map x), Function.iterate_succ_apply, pow_succ]; ring
  funext x
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  have hle (n : ℕ) : |first x - second x| ≤ discount ^ n * (firstBound + secondBound) := by
    rw [heq n x, abs_mul, abs_of_nonneg (pow_nonneg hd n)]
    exact mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans (add_le_add (hfirstBound _) (hsecondBound _))) (pow_nonneg hd n)
  exact ge_of_tendsto
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hd hd').mul_const (firstBound + secondBound))
    (Filter.Eventually.of_forall hle)

end
end Universality
