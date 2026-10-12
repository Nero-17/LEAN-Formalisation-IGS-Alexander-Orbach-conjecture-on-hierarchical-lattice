import IGSIII34.Spectral.ActualCutoffSequenceCompletion
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace IGSIII34.Spectral
noncomputable section
open Filter
open scoped Topology

/-- Integer reciprocal schedules suffice for arbitrarily small exponential
loss. This uses only geometric powers and does not round a real exponent. -/
theorem exists_rational_reciprocal_cutoff_slack_completion
    (base : ℝ) (basePositive : 0 < base) (tolerance : ℝ) (greater : 1 < tolerance) :
    ∃ slack : ℚ, 1 < (slack : ℝ) ∧ ∃ divisor : ℕ, 0 < divisor ∧
      ∀ coefficient : ℝ, 0 < coefficient → ∀ᶠ depth in atTop,
        (slack : ℝ)^depth * ((base * (slack : ℝ))^(depth / divisor) + coefficient) ≤ tolerance^depth := by
  have sqrtGreater : 1 < Real.sqrt tolerance := by
    have squareRoot := Real.sq_sqrt (zero_lt_one.trans greater).le
    have nonnegative := Real.sqrt_nonneg tolerance
    nlinarith
  obtain ⟨slack, slackGreater, slackBelow⟩ := exists_rat_btwn sqrtGreater
  have slackPositive : 0 < (slack : ℝ) := zero_lt_one.trans slackGreater
  have squareBelow : (slack : ℝ)^2 < tolerance := by
    have squareRoot := Real.sq_sqrt (zero_lt_one.trans greater).le
    have sqrtNonnegative := Real.sqrt_nonneg tolerance
    nlinarith
  have diverge := tendsto_pow_atTop_atTop_of_one_lt slackGreater
  obtain ⟨index, large⟩ := eventually_atTop.mp (diverge.eventually (eventually_ge_atTop (base * (slack : ℝ))))
  let divisor := max index 1
  have divisorPositive : 0 < divisor := by dsimp only [divisor]; omega
  have baseBound : base * (slack : ℝ) ≤ (slack : ℝ)^divisor := large divisor (le_max_left _ _)
  refine ⟨slack, slackGreater, divisor, divisorPositive, ?_⟩
  intro coefficient coefficientPositive
  have ratioGreater : 1 < tolerance / (slack : ℝ)^2 := (one_lt_div (sq_pos_of_pos slackPositive)).mpr squareBelow
  have absorbs := (tendsto_pow_atTop_atTop_of_one_lt ratioGreater).eventually
    (eventually_ge_atTop (1 + coefficient))
  filter_upwards [absorbs] with depth absorb
  have refinement : (base * (slack : ℝ))^(depth / divisor) ≤ (slack : ℝ)^depth := by
    calc
      _ ≤ ((slack : ℝ)^divisor)^(depth / divisor) :=
        pow_le_pow_left₀ (mul_pos basePositive slackPositive).le baseBound _
      _ = (slack : ℝ)^(divisor * (depth / divisor)) := (pow_mul _ _ _).symm
      _ ≤ (slack : ℝ)^depth := pow_le_pow_right₀ slackGreater.le (Nat.mul_div_le depth divisor)
  have slackAtLeastOne : 1 ≤ (slack : ℝ)^depth := one_le_pow₀ slackGreater.le
  have coefficientBound : coefficient ≤ coefficient * (slack : ℝ)^depth := by nlinarith
  have absorbed : (1 + coefficient) * ((slack : ℝ)^2)^depth ≤ tolerance^depth := by
    have normalized : 1 + coefficient ≤ tolerance^depth / ((slack : ℝ)^2)^depth := by
      simpa only [div_pow] using absorb
    exact (le_div_iff₀ (pow_pos (sq_pos_of_pos slackPositive) depth)).mp normalized
  calc
    _ ≤ (slack : ℝ)^depth * ((slack : ℝ)^depth + coefficient * (slack : ℝ)^depth) :=
      mul_le_mul_of_nonneg_left (add_le_add refinement coefficientBound) (pow_pos slackPositive depth).le
    _ = (1 + coefficient) * ((slack : ℝ)^2)^depth := by rw [← pow_mul, Nat.mul_comm 2 depth, pow_mul]; ring
    _ ≤ tolerance^depth := absorbed

end
end IGSIII34.Spectral
