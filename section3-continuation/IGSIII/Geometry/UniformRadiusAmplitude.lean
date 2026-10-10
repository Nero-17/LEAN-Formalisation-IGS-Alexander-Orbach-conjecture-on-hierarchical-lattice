import IGSIII.Geometry.UniformRadiusBound

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open scoped BigOperators

/-- A global descendant terminal envelope yields a uniform radius bound for
every remaining depth. This is proved from the actual graph radius recursion. -/
theorem marked_radius_uniform_bound_of_amplified_terminal_envelope (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (scale eta coefficient amplitude : ℝ) (start : ℕ)
    (amplitude_nonnegative : 0 ≤ amplitude)
    (scale_gt_one : 1 < scale) (eta_positive : 0 < eta)
    (growth_ge_one : 1 ≤ scale * eta)
    (coefficient_large : (rule.edges : ℝ) ≤ coefficient)
    (coefficient_contracts : eta * (coefficient + rule.edges * amplitude) ≤ coefficient)
    (terminal_envelope : ∀ address opened depth, start ≤ address.length →
      (markedTerminalDistance rule marks depth address opened : ℝ) ≤
        amplitude * scale ^ (depth + 1) * (scale * eta) ^ address.length) :
    ∀ depth address opened, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) ≤
        coefficient * scale ^ (depth + 1) * (scale * eta) ^ address.length := by
  have scale_positive := zero_lt_one.trans scale_gt_one
  have growth_positive := mul_pos scale_positive eta_positive
  have coefficient_nonnegative : 0 ≤ coefficient := (Nat.cast_nonneg rule.edges).trans coefficient_large
  intro depth
  induction depth with
  | zero =>
    intro address opened _
    have seed := markedTerminalComponentRadius_zero_le rule marks address opened
    have seed_cast : (markedTerminalComponentRadius rule marks 0 address opened : ℝ) ≤ rule.edges := by exact_mod_cast seed
    calc
      _ ≤ coefficient := seed_cast.trans coefficient_large
      _ ≤ coefficient * scale := by nlinarith
      _ ≤ coefficient * scale ^ (0 + 1) * (scale * eta) ^ address.length := by
        simpa using le_mul_of_one_le_right (mul_nonneg coefficient_nonnegative scale_positive.le)
          (one_le_pow₀ growth_ge_one)
  | succ depth induction_hypothesis =>
    intro address opened beyond
    have child_beyond (edge : Fin rule.edges) : start ≤ (address ++ [edge]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    have child_radius_bound :
        ((Finset.univ.sup (fun edge => markedTerminalComponentRadius rule marks depth
          (address ++ [edge]) (marks (address, opened) edge)) : ℕ) : ℝ) ≤
        coefficient * scale ^ (depth + 1) * (scale * eta) ^ (address.length + 1) := by
      apply cast_finset_sup_le
      · positivity
      · intro edge _
        simpa only [List.length_append, List.length_singleton] using
          induction_hypothesis (address ++ [edge]) (marks (address, opened) edge) (child_beyond edge)
    have child_distance_bound :
        ((Finset.univ.sup (fun edge => markedTerminalDistance rule marks depth
          (address ++ [edge]) (marks (address, opened) edge)) : ℕ) : ℝ) ≤
        amplitude * scale ^ (depth + 1) * (scale * eta) ^ (address.length + 1) := by
      apply cast_finset_sup_le
      · positivity
      · intro edge _
        simpa only [List.length_append, List.length_singleton] using
          terminal_envelope (address ++ [edge]) (marks (address, opened) edge) depth (child_beyond edge)
    have actual_recursion := markedTerminalComponentRadius_succ_le rule marks depth address opened
    have actual_recursion_cast :
        (markedTerminalComponentRadius rule marks (depth + 1) address opened : ℝ) ≤
        ((Finset.univ.sup (fun edge => markedTerminalComponentRadius rule marks depth
          (address ++ [edge]) (marks (address, opened) edge)) : ℕ) : ℝ) +
        (rule.edges : ℝ) * ((Finset.univ.sup (fun edge => markedTerminalDistance rule marks depth
          (address ++ [edge]) (marks (address, opened) edge)) : ℕ) : ℝ) := by
      exact_mod_cast actual_recursion
    have factor_bound : (scale * eta) * (coefficient + rule.edges * amplitude) ≤ coefficient * scale := by
      nlinarith [mul_le_mul_of_nonneg_left coefficient_contracts scale_positive.le]
    have product_bound := mul_le_mul_of_nonneg_left factor_bound
      (mul_nonneg (pow_nonneg scale_positive.le (depth + 1)) (pow_nonneg growth_positive.le address.length))
    calc
      _ ≤ _ := actual_recursion_cast
      _ ≤ coefficient * scale ^ (depth + 1) * (scale * eta) ^ (address.length + 1) +
          (rule.edges : ℝ) * (amplitude * scale ^ (depth + 1) * (scale * eta) ^ (address.length + 1)) :=
        add_le_add child_radius_bound (mul_le_mul_of_nonneg_left child_distance_bound (Nat.cast_nonneg _))
      _ ≤ coefficient * scale ^ (depth + 1 + 1) * (scale * eta) ^ address.length := by
        calc
          _ = scale ^ (depth + 1) * (scale * eta) ^ address.length *
              ((scale * eta) * (coefficient + rule.edges * amplitude)) := by
            rw [pow_succ (scale * eta) address.length]
            ring
          _ ≤ scale ^ (depth + 1) * (scale * eta) ^ address.length * (coefficient * scale) := product_bound
          _ = _ := by rw [pow_succ scale (depth + 1)]; ring

end IGSIII.Geometry

