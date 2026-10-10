import IGSIII.Chemical.SubstitutionPaths.FiveCycleInverseMoments
import IGSIII.Chemical.SmallBall.FiniteDepthGrowth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII.Chemical.FiveCycle

open Universality Universality.FiniteNetwork Substitution IGSIII.Probability
open IGSIII.Chemical.SmallBall
open scoped BigOperators

theorem inverseThirdMoment_nonnegative {vertices edges : ℕ}
    (cell : FiniteNetwork vertices edges) (p : ℝ) (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1) :
    0 ≤ inverseThirdMoment cell p := by
  apply Finset.sum_nonneg
  intro configuration _
  exact mul_nonneg (cell.conditionalCellWeight_nonneg nonnegative atMostOne true configuration)
    (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)

theorem actual_inverse_third_moment_geometric (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : network.reliability p = p) (depth : ℕ) :
    inverseThirdMoment (rule.generation depth).network p ≤
      (p / 8 + p ^ 2 / 27) ^ depth * inverseThirdMoment (rule.generation 0).network p := by
  have coefficientNonnegative : 0 ≤ p / 8 + p ^ 2 / 27 := by positivity
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      refine (actual_inverse_third_moment_recursion p positive lessOne fixedPoint depth).trans
        ((mul_le_mul_of_nonneg_left inductionHypothesis coefficientNonnegative).trans_eq ?_)
      rw [pow_succ]
      ring

theorem actual_growth_inverse_cube_constraint (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanUpper : ∀ depth, conditionedDistanceMean (rule.generation depth).network p ≤
      constant⁻¹ * growth ^ (depth + 1)) :
    1 ≤ (p / 8 + p ^ 2 / 27) * growth ^ 3 := by
  have coefficientPositive : 0 < p / 8 + p ^ 2 / 27 := by positivity
  have initialNonnegative := inverseThirdMoment_nonnegative (rule.generation 0).network p positive.le lessOne.le
  have powerComparison : ∀ depth : ℕ, ((p / 8 + p ^ 2 / 27)⁻¹) ^ depth ≤
      (inverseThirdMoment (rule.generation 0).network p * constant⁻¹ ^ 3 * growth ^ 3) * (growth ^ 3) ^ depth := by
    intro depth
    have meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
      lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]))
    have inverseBound := (actual_inverse_third_moment_lower (rule.generation depth).network p positive lessOne
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint])).trans
        (actual_inverse_third_moment_geometric p positive lessOne fixedPoint depth)
    have oneBound : 1 ≤ (p / 8 + p ^ 2 / 27) ^ depth *
        inverseThirdMoment (rule.generation 0).network p *
          conditionedDistanceMean (rule.generation depth).network p ^ 3 := by
      have scaled := mul_le_mul_of_nonneg_right inverseBound (pow_nonneg meanPositive.le 3)
      have cancellation : (conditionedDistanceMean (rule.generation depth).network p)⁻¹ ^ 3 *
          conditionedDistanceMean (rule.generation depth).network p ^ 3 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ meanPositive.ne', one_pow]
      rwa [cancellation] at scaled
    have meanCubeUpper : conditionedDistanceMean (rule.generation depth).network p ^ 3 ≤
        constant⁻¹ ^ 3 * (growth ^ 3) ^ (depth + 1) := by
      refine (pow_le_pow_left₀ meanPositive.le (meanUpper depth) 3).trans_eq ?_
      rw [mul_pow, pow_right_comm]
    have enlarged := oneBound.trans (mul_le_mul_of_nonneg_left meanCubeUpper
      (mul_nonneg (pow_nonneg coefficientPositive.le depth) initialNonnegative))
    have cancellation : ((p / 8 + p ^ 2 / 27)⁻¹) ^ depth * (p / 8 + p ^ 2 / 27) ^ depth = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ coefficientPositive.ne', one_pow]
    calc
      _ = ((p / 8 + p ^ 2 / 27)⁻¹) ^ depth * 1 := by ring
      _ ≤ ((p / 8 + p ^ 2 / 27)⁻¹) ^ depth *
          ((p / 8 + p ^ 2 / 27) ^ depth * inverseThirdMoment (rule.generation 0).network p *
            (constant⁻¹ ^ 3 * (growth ^ 3) ^ (depth + 1))) :=
        mul_le_mul_of_nonneg_left enlarged (pow_nonneg (inv_nonneg.mpr coefficientPositive.le) depth)
      _ = (((p / 8 + p ^ 2 / 27)⁻¹) ^ depth * (p / 8 + p ^ 2 / 27) ^ depth) *
          inverseThirdMoment (rule.generation 0).network p * constant⁻¹ ^ 3 * growth ^ 3 * (growth ^ 3) ^ depth := by
        rw [pow_succ]
        ring
      _ = _ := by rw [cancellation]; ring
  have baseComparison := base_le_of_uniform_pow_comparison (pow_pos growthPositive 3) powerComparison
  have multiplied := mul_le_mul_of_nonneg_left baseComparison coefficientPositive.le
  simpa only [mul_inv_cancel₀ coefficientPositive.ne'] using multiplied

theorem coefficient_cubic_root_gt_two (p : ℝ) (positive : 0 < p)
    (criticalEquation : p ^ 3 + p ^ 2 = 1) :
    2 < (p / 8 + p ^ 2 / 27) ^ (-(1 / (3 : ℝ))) := by
  have coefficientPositive : 0 < p / 8 + p ^ 2 / 27 := by positivity
  have rootPositive := Real.rpow_pos_of_pos coefficientPositive (-(1 / (3 : ℝ)))
  have rootCube : ((p / 8 + p ^ 2 / 27) ^ (-(1 / (3 : ℝ)))) ^ 3 =
      (p / 8 + p ^ 2 / 27)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul coefficientPositive.le]
    norm_num [Real.rpow_neg_one]
  apply scaling_factor_gt_two_of_inverse_moment_bound positive criticalEquation rootPositive
  rw [rootCube, mul_inv_cancel₀ coefficientPositive.ne']

theorem actual_growth_lower_bound (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanUpper : ∀ depth, conditionedDistanceMean (rule.generation depth).network p ≤
      constant⁻¹ * growth ^ (depth + 1)) :
    (p / 8 + p ^ 2 / 27) ^ (-(1 / (3 : ℝ))) ≤ growth ∧ 2 < growth := by
  have coefficientPositive : 0 < p / 8 + p ^ 2 / 27 := by positivity
  have constraint := actual_growth_inverse_cube_constraint p positive lessOne fixedPoint
    constant growth growthPositive meanUpper
  have inverseComparison : (p / 8 + p ^ 2 / 27)⁻¹ ≤ growth ^ 3 := by
    have multiplied := mul_le_mul_of_nonneg_left constraint (inv_nonneg.mpr coefficientPositive.le)
    simpa only [mul_one, ← mul_assoc, inv_mul_cancel₀ coefficientPositive.ne', one_mul] using multiplied
  have comparison := Real.rpow_le_rpow (inv_nonneg.mpr coefficientPositive.le) inverseComparison
    (by norm_num : 0 ≤ (1 / (3 : ℝ)))
  have leftIdentity : ((p / 8 + p ^ 2 / 27)⁻¹) ^ (1 / (3 : ℝ)) =
      (p / 8 + p ^ 2 / 27) ^ (-(1 / (3 : ℝ))) := by
    rw [Real.inv_rpow coefficientPositive.le, Real.rpow_neg coefficientPositive.le]
  have rightIdentity : (growth ^ 3) ^ (1 / (3 : ℝ)) = growth := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul growthPositive.le]
    norm_num
  rw [leftIdentity, rightIdentity] at comparison
  exact ⟨comparison, (coefficient_cubic_root_gt_two p positive
    ((actual_fixedPoint_iff positive lessOne).mp fixedPoint)).trans_le comparison⟩

theorem exists_actual_growth_strictly_above_two (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (p / 8 + p ^ 2 / 27) ^ (-(1 / (3 : ℝ))) ≤ growth ∧ 2 < growth ∧
      growth ≤ longestTerminalPath network ∧ ∀ depth,
        growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
          manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, bounds⟩ :=
    exists_actual_chemical_growth rule rule_classical p positive lessOne fixedPoint
  have growthPositive : 0 < growth := by
    change (network.fullGraph.dist network.source network.target : ℝ) ≤ growth at growthLower
    rw [terminal_distance] at growthLower
    norm_num at growthLower
    linarith
  have strictLower := actual_growth_lower_bound p positive lessOne fixedPoint constant growth
    growthPositive (fun depth => (bounds (depth + 1)).2)
  exact ⟨constant, growth, constantPositive, constantAtMostOne, strictLower.1, strictLower.2, growthUpper, bounds⟩

end IGSIII.Chemical.FiveCycle
