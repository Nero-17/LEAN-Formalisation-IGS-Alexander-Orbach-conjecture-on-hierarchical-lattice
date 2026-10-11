import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section

/-- The constant shift absorbs all bounded rewards when every row has mass at least two. -/
theorem affine_population_lower_comparison {State : Type*} [Fintype State]
    (matrix : ℕ → State → State → ℝ) (reward : ℕ → State → ℝ)
    (coarse fine : ℕ → State → ℝ) (bound scale : ℝ)
    (hbound : 0 ≤ bound) (hscale : 0 ≤ scale)
    (hmatrix : ∀ n i j, 0 ≤ matrix n i j)
    (hrows : ∀ n i, 2 ≤ ∑ j, matrix n i j)
    (hreward : ∀ n i, 0 ≤ reward n i ∧ reward n i ≤ bound)
    (hcoarse : ∀ n i, coarse (n + 1) i = reward n i + ∑ j, matrix n i j * coarse n j)
    (hfine : ∀ n i, fine (n + 1) i = reward n i + ∑ j, matrix n i j * fine n j)
    (hstart : ∀ i, scale * (coarse 0 i + bound) ≤ fine 0 i) :
    ∀ n i, scale * (coarse n i + bound) ≤ fine n i := by
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih =>
    intro i
    rw [hcoarse, hfine]
    have hrow : reward n i + bound ≤ ∑ j, matrix n i j * bound := by
      rw [← Finset.sum_mul]
      nlinarith [mul_le_mul_of_nonneg_right (hrows n i) hbound, (hreward n i).2]
    calc
      _ ≤ scale * ((∑ j, matrix n i j * coarse n j) + ∑ j, matrix n i j * bound) := by
        apply mul_le_mul_of_nonneg_left _ hscale
        linarith
      _ = ∑ j, matrix n i j * (scale * (coarse n j + bound)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j, matrix n i j * fine n j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ih j) (hmatrix n i j))
      _ ≤ _ := le_add_of_nonneg_left (hreward n i).1

end
end Universality
