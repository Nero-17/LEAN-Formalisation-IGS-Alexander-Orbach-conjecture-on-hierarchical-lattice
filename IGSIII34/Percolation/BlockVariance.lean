import IGSIII34.Percolation.BlockResistance
import IGSIII34.Percolation.ConfigurationMixture
import IGSIII34.Percolation.MeanGrowthSteps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open IGSIII.Chemical.Substitution
open scoped BigOperators

theorem generation_block_electrical_residual_variance_bound
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight parameter true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network parameter configuration)^2) ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight parameter true)
      (fun configuration => (positiveNormalizedResistance (rule.generation fine).network parameter configuration)⁻¹^power) ≤ inverseMoment) :
    finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
      (fun configuration =>
        (normalizedConfigurationResistance (rule.generation (coarse+fine+1)).network parameter configuration -
          electricalBlockConditionalMean rule parameter coarse fine (generationBlockCoarse rule coarse fine configuration))^2) ≤
      2*secondMoment*Real.sqrt secondMoment *
        (((rule.generation coarse).edges : ℝ)*inverseMoment)^(1/power) *
          (conditionalMeanResistance (rule.generation fine).network parameter /
            conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter) := by
  have innerPositive := generation_conditionalMeanResistance_positive rule classical parameter positive belowOne fixedPoint fine
  have parentPositive := generation_conditionalMeanResistance_positive rule classical parameter positive belowOne fixedPoint (coarse+fine+1)
  have secondEquality :
      finiteMean ((rule.generation coarse).network.conditionalCellWeight parameter true) (fun outerConfiguration =>
        finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
          (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
            electricalCell (rule.generation coarse).network outerConfiguration
              (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge))^2)) =
        (conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter /
          conditionalMeanResistance (rule.generation fine).network parameter)^2 *
            finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
              (fun configuration => (normalizedConfigurationResistance (rule.generation (coarse+fine+1)).network parameter configuration)^2) := by
    rw [← normalized_generation_block_resistance_observable rule parameter positive belowOne fixedPoint coarse fine innerPositive (fun value => value^2)]
    have scaled (configuration : Configuration (rule.generation (coarse+fine+1)).edges) :
        (unitConfigurationResistance (rule.generation (coarse+fine+1)).network configuration /
          conditionalMeanResistance (rule.generation fine).network parameter)^2 =
        (conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter /
          conditionalMeanResistance (rule.generation fine).network parameter)^2 *
            (normalizedConfigurationResistance (rule.generation (coarse+fine+1)).network parameter configuration)^2 := by
      unfold normalizedConfigurationResistance
      field_simp
    simp_rw [scaled]
    exact finiteMean_const_mul _ _ _
  have mixture := finite_electricalCell_mixture_variance_le_product_moments
    (rule.generation coarse).network ((rule.generation coarse).network.conditionalCellWeight parameter true)
    ((rule.generation coarse).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
    ((rule.generation coarse).network.sum_conditionalCellWeight parameter
      (by rwa [rule.generation_fixed_point parameter fixedPoint])
      (by rwa [rule.generation_fixed_point parameter fixedPoint]) true)
    (fun configuration notCrossing => by simp [conditionalCellWeight, notCrossing])
    ((rule.generation fine).network.conditionalCellWeight parameter true)
    ((rule.generation fine).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
    ((rule.generation fine).network.sum_conditionalCellWeight parameter
      (by rwa [rule.generation_fixed_point parameter fixedPoint])
      (by rwa [rule.generation_fixed_point parameter fixedPoint]) true)
    (positiveNormalizedResistance (rule.generation fine).network parameter)
    (positiveNormalizedResistance_positive _ parameter innerPositive)
    powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
    (secondMomentBound fine) inverseMomentBound
  rw [secondEquality, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (div_nonneg parentPositive.le innerPositive.le)] at mixture
  rw [generation_block_electrical_residual_second_moment rule classical parameter positive belowOne fixedPoint]
  have scaledBound := mul_le_mul_of_nonneg_left mixture
    (sq_nonneg (conditionalMeanResistance (rule.generation fine).network parameter /
      conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter))
  apply scaledBound.trans
  have parentSecondBound := secondMomentBound (coarse+fine+1)
  rw [positiveNormalizedResistance_observable _ parameter (fun value => value^2)] at parentSecondBound
  have comparison := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt parentSecondBound)
        (mul_nonneg (by norm_num : (0 : ℝ)≤2) secondMomentNonnegative))
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg (rule.generation coarse).edges) inverseMomentNonnegative) (1/power)))
    (div_nonneg innerPositive.le parentPositive.le)
  refine le_trans ?_ comparison
  apply le_of_eq
  field_simp

theorem generation_block_electrical_residual_variance_geometric (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)^2) ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
      (fun configuration =>
        (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p configuration -
          electricalBlockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration)) ^ 2) ≤
      (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power)) *
        (((rule.edges : ℝ) ^ (1 / power)) / deriv rule.network.reliability p) ^ (coarse + 1) := by
  have derivativePositive : 0 < deriv rule.network.reliability p :=
    zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint classical.scale)
  have bound := generation_block_electrical_residual_variance_bound rule classical p positive lessOne fixedPoint coarse fine
    powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
    secondMomentBound inverseMomentBound
  refine bound.trans ?_
  have comparison := generation_block_electrical_mean_ratio_decay rule classical p positive lessOne fixedPoint coarse fine
  refine (mul_le_mul_of_nonneg_left comparison ?_).trans_eq ?_
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) secondMomentNonnegative)
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) inverseMomentNonnegative) _)
  · rw [rule.generation_edges, Nat.cast_pow,
      Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _) inverseMomentNonnegative,
      ← Real.rpow_pow_comm (Nat.cast_nonneg _), div_pow]
    ring


end
end IGSIII34.Percolation
