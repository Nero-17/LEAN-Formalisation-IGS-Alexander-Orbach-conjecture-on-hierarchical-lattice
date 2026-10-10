import IGSIII.Chemical.SmallBall.PairedPathBarrier

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open scoped BigOperators

noncomputable section

theorem exists_uniform_finite_paired_exponential_barrier
    {Index : Type*} {Outcome : Index → Type*} [∀ index, Fintype (Outcome index)]
    (weight first second : (index : Index) → Outcome index → ℝ)
    (weightNonnegative : ∀ index outcome, 0 ≤ weight index outcome)
    (secondNonnegative : ∀ index outcome, 0 ≤ second index outcome)
    {parameter : ℝ} (parameterPositive : 0 < parameter)
    (exponentialBound : ∃ bound : ℝ, ∀ index,
      (∑ outcome, weight index outcome * Real.exp (2 * parameter * first index outcome)) ≤ bound)
    (laplaceDecay : ∀ target : ℝ, 0 < target → ∃ laplaceParameter : ℝ, 0 < laplaceParameter ∧ ∀ index,
      (∑ outcome, weight index outcome * Real.exp (-laplaceParameter * second index outcome)) ≤ target)
    {ratio : ℝ} (ratioPositive : 0 < ratio) :
    ∃ scale : ℝ, 1 ≤ scale ∧ ∀ index,
      (∑ outcome, weight index outcome * Real.exp (parameter * (first index outcome - scale * second index outcome))) ≤ ratio := by
  obtain ⟨bound, boundValid⟩ := exponentialBound
  have boundPositive : 0 < max 1 bound := zero_lt_one.trans_le (le_max_left _ _)
  have sqrtPositive : 0 < Real.sqrt (max 1 bound) := Real.sqrt_pos.mpr boundPositive
  have targetPositive : 0 < (ratio / Real.sqrt (max 1 bound)) ^ 2 :=
    sq_pos_of_pos (div_pos ratioPositive sqrtPositive)
  obtain ⟨laplaceParameter, laplaceParameterPositive, laplaceValid⟩ :=
    laplaceDecay _ targetPositive
  refine ⟨max 1 (laplaceParameter / (2 * parameter)), le_max_left _ _, fun index => ?_⟩
  have coefficientBound : laplaceParameter ≤ 2 * parameter * max 1 (laplaceParameter / (2 * parameter)) := by
    have comparison := (div_le_iff₀ (by positivity : 0 < 2 * parameter)).mp
      (le_max_right 1 (laplaceParameter / (2 * parameter)))
    simpa only [mul_comm] using comparison
  have firstBound : (∑ outcome, weight index outcome * Real.exp (2 * parameter * first index outcome)) ≤ max 1 bound :=
    (boundValid index).trans (le_max_right _ _)
  have secondBound : (∑ outcome, weight index outcome *
      Real.exp (-2 * parameter * max 1 (laplaceParameter / (2 * parameter)) * second index outcome)) ≤
        (ratio / Real.sqrt (max 1 bound)) ^ 2 := by
    refine (Finset.sum_le_sum (fun outcome _ => ?_)).trans (laplaceValid index)
    apply mul_le_mul_of_nonneg_left _ (weightNonnegative index outcome)
    apply Real.exp_le_exp.mpr
    have multiplied := mul_le_mul_of_nonneg_right coefficientBound (secondNonnegative index outcome)
    nlinarith
  have comparison := finite_paired_exponential_le_of_marginals (weight index) (first index) (second index)
    (weightNonnegative index) parameter (max 1 (laplaceParameter / (2 * parameter)))
    (max 1 bound) ((ratio / Real.sqrt (max 1 bound)) ^ 2) firstBound secondBound
  have identity : Real.sqrt (max 1 bound) * Real.sqrt ((ratio / Real.sqrt (max 1 bound)) ^ 2) = ratio := by
    rw [Real.sqrt_sq (div_nonneg ratioPositive.le sqrtPositive.le)]
    field_simp
  exact comparison.trans_eq identity

theorem geometric_power_geometric_summable {base : ℕ} (baseAtLeastTwo : 2 ≤ base)
    {ratio : ℝ} (ratioNonnegative : 0 ≤ ratio) (ratioBelowOne : ratio < 1) :
    Summable (fun depth : ℕ => ratio ^ (base ^ depth)) := by
  have exponentLower (depth : ℕ) : depth + 1 ≤ base ^ depth := by
    induction depth with
    | zero => simp
    | succ depth inductionHypothesis =>
        rw [pow_succ]
        have multiplied := Nat.mul_le_mul_right (base ^ depth) baseAtLeastTwo
        nlinarith
  apply Summable.of_nonneg_of_le (fun depth => pow_nonneg ratioNonnegative _)
    (fun depth => pow_le_pow_of_le_one ratioNonnegative ratioBelowOne.le (exponentLower depth))
  simpa only [pow_succ] using (summable_geometric_of_lt_one ratioNonnegative ratioBelowOne).mul_right ratio

end
end IGSIII.Chemical.SmallBall
