import IGSIII.Chemical.SubstitutionPaths.BlockConditioning
import IGSIII.Chemical.SubstitutionPaths.NormalizedVariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped BigOperators

theorem networkEquivalence_conditionedDistanceMean
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (p : ℝ) :
    conditionedDistanceMean second p = conditionedDistanceMean first p := by
  unfold conditionedDistanceMean
  rw [← equivalence.configuration.sum_comp]
  simp only [NetworkEquivalence.conditionalCellWeight, networkEquivalence_terminal_distance_all]

theorem networkEquivalence_normalizedDistanceMoment
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (p : ℝ) (order : ℕ) :
    normalizedDistanceMoment second p order = normalizedDistanceMoment first p order := by
  unfold normalizedDistanceMoment normalizedDistance
  rw [← equivalence.configuration.sum_comp, networkEquivalence_conditionedDistanceMean equivalence]
  simp only [NetworkEquivalence.conditionalCellWeight, networkEquivalence_terminal_distance_all]

theorem generation_conditionedDistanceMean_growth (rule : Rule)
    (simple : Function.Injective (fun edge => s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (derivativeNonnegative : 0 ≤ deriv rule.network.reliability p) (fine steps : ℕ) :
    deriv rule.network.reliability p ^ steps * conditionedDistanceMean (rule.generation fine).network p ≤
      conditionedDistanceMean (rule.generation (fine + steps)).network p := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      have meanPositive : 0 < conditionedDistanceMean (rule.generation (fine + steps)).network p :=
        lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint]))
      have ratio := (generation_conditionedDistanceMean_ratio_bounds rule simple p positive lessOne fixedPoint
        (fine + steps)).1
      have stepBound := (le_div_iff₀ meanPositive).mp ratio
      calc
        _ = deriv rule.network.reliability p *
            (deriv rule.network.reliability p ^ steps * conditionedDistanceMean (rule.generation fine).network p) := by
          rw [pow_succ]
          ring
        _ ≤ deriv rule.network.reliability p * conditionedDistanceMean (rule.generation (fine + steps)).network p :=
          mul_le_mul_of_nonneg_left inductionHypothesis derivativeNonnegative
        _ ≤ _ := stepBound

theorem generation_block_mean_ratio_decay (rule : Rule)
    (simple : Function.Injective (fun edge => s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (derivativePositive : 0 < deriv rule.network.reliability p) (coarse fine : ℕ) :
    conditionedDistanceMean (rule.generation fine).network p /
      conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p ≤
        1 / deriv rule.network.reliability p ^ (coarse + 1) := by
  have parentMeanPositive : 0 < conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have growth := generation_conditionedDistanceMean_growth rule simple p positive lessOne fixedPoint
    derivativePositive.le fine (coarse + 1)
  apply (div_le_div_iff₀ parentMeanPositive (pow_pos derivativePositive _)).mpr
  rw [show fine + (coarse + 1) = coarse + fine + 1 by omega] at growth
  simpa only [one_mul, mul_comm] using growth

theorem generation_block_residual_variance_bound (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, normalizedDistanceMoment (rule.generation depth).network p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
      (fun configuration =>
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p configuration -
          blockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration)) ^ 2) ≤
      2 * secondMoment * Real.sqrt secondMoment *
        (((rule.generation coarse).edges : ℝ) * inverseMoment) ^ (1 / power) *
          (conditionedDistanceMean (rule.generation fine).network p /
            conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p) := by
  rw [generation_block_residual_second_moment rule classical p positive lessOne fixedPoint]
  have bound := actual_substitution_normalized_conditional_variance_bound
    (rule.generation coarse).network (rule.generation fine).network (classical.generation coarse).simple
    p positive lessOne (rule.generation_fixed_point p fixedPoint coarse)
    (rule.generation_fixed_point p fixedPoint fine) powerAtLeastTwo secondMoment inverseMoment
    secondMomentNonnegative inverseMomentNonnegative (secondMomentBound fine) inverseMomentBound
  rw [networkEquivalence_conditionedDistanceMean (rule.generationBlockDecomposition coarse fine),
    networkEquivalence_normalizedDistanceMoment (rule.generationBlockDecomposition coarse fine)] at bound
  refine bound.trans ?_
  have ratioNonnegative : 0 ≤ conditionedDistanceMean (rule.generation fine).network p /
      conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p := by
    apply div_nonneg
    all_goals exact le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (secondMomentBound _))
        (mul_nonneg (by norm_num) secondMomentNonnegative))
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) inverseMomentNonnegative) _)) ratioNonnegative

theorem generation_block_residual_variance_geometric (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, normalizedDistanceMoment (rule.generation depth).network p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
      (fun configuration =>
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p configuration -
          blockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration)) ^ 2) ≤
      (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power)) *
        (((rule.edges : ℝ) ^ (1 / power)) / deriv rule.network.reliability p) ^ (coarse + 1) := by
  have derivativePositive : 0 < deriv rule.network.reliability p :=
    zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint classical.scale)
  have bound := generation_block_residual_variance_bound rule classical p positive lessOne fixedPoint coarse fine
    powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
    secondMomentBound inverseMomentBound
  refine bound.trans ?_
  have comparison := generation_block_mean_ratio_decay rule classical.simple p positive lessOne fixedPoint
    derivativePositive coarse fine
  refine (mul_le_mul_of_nonneg_left comparison ?_).trans_eq ?_
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) secondMomentNonnegative)
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) inverseMomentNonnegative) _)
  · rw [rule.generation_edges, Nat.cast_pow,
      Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _) inverseMomentNonnegative,
      ← Real.rpow_pow_comm (Nat.cast_nonneg _), div_pow]
    ring

end IGSIII.Chemical.Substitution
