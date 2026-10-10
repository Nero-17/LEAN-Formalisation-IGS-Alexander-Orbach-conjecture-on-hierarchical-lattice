import IGSIII.Chemical.SmallBall.FiniteDepthGrowth

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork
open scoped BigOperators

noncomputable section

def growthScaledDistance (rule : Rule) (growth : ℝ) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges) : ℝ :=
  ((rule.generation depth).network.openGraph configuration).dist
      (rule.generation depth).network.source (rule.generation depth).network.target /
    growth ^ (depth + 1)

theorem growthScaledDistance_nonnegative (rule : Rule) (growth : ℝ)
    (growthNonnegative : 0 ≤ growth) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges) :
    0 ≤ growthScaledDistance rule growth depth configuration :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg growthNonnegative _)

theorem growthScaledDistance_eq_mean_ratio (rule : Rule) (p growth : ℝ)
    (growthPositive : 0 < growth) (depth : ℕ)
    (meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p)
    (configuration : Configuration (rule.generation depth).edges) :
    growthScaledDistance rule growth depth configuration =
      (conditionedDistanceMean (rule.generation depth).network p / growth ^ (depth + 1)) *
        normalizedDistance (rule.generation depth).network p configuration := by
  dsimp [growthScaledDistance, normalizedDistance]
  field_simp

theorem growthScaledDistance_bounds (rule : Rule) (p constant growth : ℝ)
    (growthPositive : 0 < growth) (depth : ℕ)
    (meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p)
    (lower : growth ^ (depth + 1) ≤ conditionedDistanceMean (rule.generation depth).network p)
    (upper : conditionedDistanceMean (rule.generation depth).network p ≤ constant⁻¹ * growth ^ (depth + 1))
    (configuration : Configuration (rule.generation depth).edges) :
    normalizedDistance (rule.generation depth).network p configuration ≤
        growthScaledDistance rule growth depth configuration ∧
      growthScaledDistance rule growth depth configuration ≤
        constant⁻¹ * normalizedDistance (rule.generation depth).network p configuration := by
  rw [growthScaledDistance_eq_mean_ratio rule p growth growthPositive depth meanPositive]
  have ratioLower : 1 ≤ conditionedDistanceMean (rule.generation depth).network p / growth ^ (depth + 1) :=
    (one_le_div (pow_pos growthPositive _)).mpr lower
  have ratioUpper : conditionedDistanceMean (rule.generation depth).network p / growth ^ (depth + 1) ≤ constant⁻¹ :=
    (div_le_iff₀ (pow_pos growthPositive _)).mpr upper
  have nonnegative := normalizedDistance_nonnegative (rule.generation depth).network meanPositive.le configuration
  exact ⟨by simpa only [one_mul] using mul_le_mul_of_nonneg_right ratioLower nonnegative,
    mul_le_mul_of_nonneg_right ratioUpper nonnegative⟩

theorem growthScaledDistance_inverse_le (rule : Rule) (p constant growth : ℝ)
    (growthPositive : 0 < growth) (depth : ℕ)
    (meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p)
    (lower : growth ^ (depth + 1) ≤ conditionedDistanceMean (rule.generation depth).network p)
    (upper : conditionedDistanceMean (rule.generation depth).network p ≤ constant⁻¹ * growth ^ (depth + 1))
    (configuration : Configuration (rule.generation depth).edges) :
    (growthScaledDistance rule growth depth configuration)⁻¹ ≤
      (normalizedDistance (rule.generation depth).network p configuration)⁻¹ := by
  by_cases zero : normalizedDistance (rule.generation depth).network p configuration = 0
  · rw [growthScaledDistance_eq_mean_ratio rule p growth growthPositive depth meanPositive, zero, mul_zero]
  · have normalizedPositive : 0 < normalizedDistance (rule.generation depth).network p configuration :=
      lt_of_le_of_ne (normalizedDistance_nonnegative _ meanPositive.le configuration) (Ne.symm zero)
    have comparison := (growthScaledDistance_bounds rule p constant growth growthPositive depth meanPositive lower upper configuration).1
    exact (inv_le_inv₀ (normalizedPositive.trans_le comparison) normalizedPositive).mpr comparison

theorem exists_uniform_growth_scaled_positive_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        growthScaledDistance rule growth depth configuration ^ power) ≤ bound := by
  obtain ⟨bound, valid⟩ := exists_uniform_generation_positive_moment rule classical.simple p positive lessOne fixedPoint classical.scale power
  refine ⟨constant⁻¹ ^ power * bound, fun depth => ?_⟩
  have meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    (pow_pos growthPositive (depth + 1)).trans_le (meanBounds (depth + 1)).1
  have comparison : (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
      growthScaledDistance rule growth depth configuration ^ power) ≤
      constant⁻¹ ^ power * normalizedDistanceMoment (rule.generation depth).network p power := by
    rw [normalizedDistanceMoment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro configuration _
    have bound := pow_le_pow_left₀ (growthScaledDistance_nonnegative rule growth growthPositive.le depth configuration)
      (growthScaledDistance_bounds rule p constant growth growthPositive depth meanPositive
        (meanBounds (depth + 1)).1 (meanBounds (depth + 1)).2 configuration).2 power
    have weighted := mul_le_mul_of_nonneg_left bound
      ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    simpa only [mul_pow, mul_assoc, mul_left_comm] using weighted
  exact comparison.trans (mul_le_mul_of_nonneg_left (valid depth) (by positivity))

theorem exists_uniform_growth_scaled_inverse_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        (growthScaledDistance rule growth depth configuration)⁻¹ ^ power) ≤ bound := by
  obtain ⟨bound, valid⟩ := exists_uniform_generation_inverse_moment rule classical.simple p positive lessOne fixedPoint classical.scale power
  refine ⟨bound, fun depth => ?_⟩
  have meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    (pow_pos growthPositive (depth + 1)).trans_le (meanBounds (depth + 1)).1
  refine (Finset.sum_le_sum (fun configuration _ => ?_)).trans (valid depth)
  apply mul_le_mul_of_nonneg_left _
    ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (growthScaledDistance_nonnegative rule growth growthPositive.le depth configuration))
    (growthScaledDistance_inverse_le rule p constant growth growthPositive depth meanPositive
      (meanBounds (depth + 1)).1 (meanBounds (depth + 1)).2 configuration) power

theorem exists_uniform_growth_scaled_factorial_moments (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (constantAtMostOne : constant ≤ 1)
    (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
    ∃ factorialConstant : ℝ, 1 ≤ factorialConstant ∧ ∀ depth power,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        growthScaledDistance rule growth depth configuration ^ power) ≤
          factorialConstant ^ power * (power.factorial : ℝ) := by
  obtain ⟨factorialConstant, atLeastOne, valid⟩ := exists_uniform_generation_factorial_moments
    rule classical.simple p positive lessOne fixedPoint classical.scale
  have inverseAtLeastOne : 1 ≤ constant⁻¹ := (one_le_inv₀ constantPositive).mpr constantAtMostOne
  refine ⟨constant⁻¹ * factorialConstant, one_le_mul_of_one_le_of_one_le inverseAtLeastOne atLeastOne, fun depth power => ?_⟩
  have meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    (pow_pos growthPositive (depth + 1)).trans_le (meanBounds (depth + 1)).1
  have comparison : (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
      growthScaledDistance rule growth depth configuration ^ power) ≤
      constant⁻¹ ^ power * normalizedDistanceMoment (rule.generation depth).network p power := by
    rw [normalizedDistanceMoment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro configuration _
    have bound := pow_le_pow_left₀ (growthScaledDistance_nonnegative rule growth growthPositive.le depth configuration)
      (growthScaledDistance_bounds rule p constant growth growthPositive depth meanPositive
        (meanBounds (depth + 1)).1 (meanBounds (depth + 1)).2 configuration).2 power
    have weighted := mul_le_mul_of_nonneg_left bound
      ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    simpa only [mul_pow, mul_assoc, mul_left_comm] using weighted
  exact comparison.trans (by
    simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left (valid depth power)
      (pow_nonneg (inv_nonneg.mpr constantPositive.le) power))

theorem exists_uniform_growth_scaled_real_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) (exponent : ℝ) :
    ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        growthScaledDistance rule growth depth configuration ^ exponent) ≤ bound := by
  by_cases exponentNonnegative : 0 ≤ exponent
  · obtain ⟨power, exponentBound⟩ := exists_nat_ge exponent
    obtain ⟨bound, valid⟩ := exists_uniform_growth_scaled_positive_moment
      rule classical p positive lessOne fixedPoint constant growth constantPositive growthPositive meanBounds power
    refine ⟨1 + bound, fun depth => ?_⟩
    letI : MeasurableSpace (Configuration (rule.generation depth).edges) := ⊤
    have comparison := finite_rpow_le_one_add_power
      ((rule.generation depth).network.conditionalCellWeight p true)
      (growthScaledDistance rule growth depth)
      (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
      ((rule.generation depth).network.sum_conditionalCellWeight p
        (by rwa [rule.generation_fixed_point p fixedPoint]) (by rwa [rule.generation_fixed_point p fixedPoint]) true)
      (growthScaledDistance_nonnegative rule growth growthPositive.le depth) exponentNonnegative exponentBound
    exact comparison.trans (by linarith [valid depth])
  · obtain ⟨power, exponentBound⟩ := exists_nat_ge (-exponent)
    obtain ⟨bound, valid⟩ := exists_uniform_growth_scaled_inverse_moment
      rule classical p positive lessOne fixedPoint constant growth growthPositive meanBounds power
    refine ⟨1 + bound, fun depth => ?_⟩
    letI : MeasurableSpace (Configuration (rule.generation depth).edges) := ⊤
    have comparison := finite_rpow_le_one_add_power
      ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (growthScaledDistance rule growth depth configuration)⁻¹)
      (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
      ((rule.generation depth).network.sum_conditionalCellWeight p
        (by rwa [rule.generation_fixed_point p fixedPoint]) (by rwa [rule.generation_fixed_point p fixedPoint]) true)
      (fun configuration => inv_nonneg.mpr (growthScaledDistance_nonnegative rule growth growthPositive.le depth configuration))
      (neg_nonneg.mpr (le_of_not_ge exponentNonnegative)) exponentBound
    simp only [← Real.rpow_neg_eq_inv_rpow, neg_neg] at comparison
    exact comparison.trans (by linarith [valid depth])

theorem exists_uniform_growth_scaled_exponential_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (parameter : ℝ) (parameterNonnegative : 0 ≤ parameter) :
    ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        Real.exp (parameter * growthScaledDistance rule growth depth configuration)) ≤ bound := by
  obtain ⟨bound, valid⟩ := exists_uniform_generation_exponential_moment rule classical.simple p positive lessOne fixedPoint classical.scale
    (parameter * constant⁻¹) (mul_nonneg parameterNonnegative (inv_nonneg.mpr constantPositive.le))
  refine ⟨bound, fun depth => ?_⟩
  have meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    (pow_pos growthPositive (depth + 1)).trans_le (meanBounds (depth + 1)).1
  refine (Finset.sum_le_sum (fun configuration _ => ?_)).trans (valid depth)
  apply mul_le_mul_of_nonneg_left _
    ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (growthScaledDistance_bounds rule p constant growth growthPositive depth meanPositive
      (meanBounds (depth + 1)).1 (meanBounds (depth + 1)).2 configuration).2 parameterNonnegative

theorem exists_uniform_growth_scaled_laplace_decay (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    {target : ℝ} (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        Real.exp (-parameter * growthScaledDistance rule growth depth configuration)) ≤ target := by
  obtain ⟨parameter, parameterPositive, valid⟩ := exists_uniform_generation_laplace_decay
    rule classical.simple p positive lessOne fixedPoint classical.scale targetPositive
  refine ⟨parameter, parameterPositive, fun depth => ?_⟩
  have meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    (pow_pos growthPositive (depth + 1)).trans_le (meanBounds (depth + 1)).1
  refine (Finset.sum_le_sum (fun configuration _ => ?_)).trans (valid depth)
  apply mul_le_mul_of_nonneg_left _
    ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (growthScaledDistance_bounds rule p constant growth growthPositive depth meanPositive
      (meanBounds (depth + 1)).1 (meanBounds (depth + 1)).2 configuration).1 (neg_nonpos.mpr parameterPositive.le)

end
end IGSIII.Chemical.SmallBall
