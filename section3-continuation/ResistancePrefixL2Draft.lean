import IGSIII34.Percolation.BlockVariance
import IGSIII.Chemical.SubstitutionPaths.CommonPrefixL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII34.Probability IGSIII.Probability IGSIII.Chemical.Substitution
open scoped BigOperators ENNReal

theorem marked_electrical_prefix_residual_norm_sq (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (coarse fine : ℕ) :
    ‖markedObservableLp rule p positive lessOne fixedPoint (coarse + fine + 1) address true
        (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p) -
      markedObservableLp rule p positive lessOne fixedPoint coarse address true
        (electricalBlockConditionalMean rule p coarse fine)‖ ^ 2 =
      IGSIII34.Probability.finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
        (fun configuration =>
          (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p configuration -
            electricalBlockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration)) ^ 2) := by
  rw [lp_norm_sq_eq_integral]
  refine (integral_congr_ae ?_).trans
    (independentInnovationLaw_marked_observable rule p positive lessOne fixedPoint
      (coarse + fine + 1) address true _)
  filter_upwards [Lp.coeFn_sub
      (markedObservableLp rule p positive lessOne fixedPoint (coarse + fine + 1) address true
        (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p))
      (markedObservableLp rule p positive lessOne fixedPoint coarse address true (electricalBlockConditionalMean rule p coarse fine)),
    markedObservableLp_ae rule p positive lessOne fixedPoint (coarse + fine + 1) address true
      (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p),
    markedObservableLp_ae rule p positive lessOne fixedPoint coarse address true (electricalBlockConditionalMean rule p coarse fine),
    marked_generationBlockCoarse_eq_ae rule p positive lessOne fixedPoint]
      with marks subtraction distanceEquality meanEquality coarseEquality
  rw [subtraction, Pi.sub_apply, distanceEquality, meanEquality, coarseEquality address true coarse fine]

theorem marked_electrical_prefix_conditionalMean_norm_sq_le (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (coarse fine : ℕ) :
    ‖markedObservableLp rule p positive lessOne fixedPoint coarse address true
      (electricalBlockConditionalMean rule p coarse fine)‖ ^ 2 ≤
        IGSIII34.Probability.finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
          (fun configuration => (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p configuration)^2) := by
  rw [markedObservableLp_norm_sq]
  exact generation_block_electrical_conditionalMean_second_moment rule classical p positive lessOne fixedPoint coarse fine

theorem marked_electrical_prefix_residual_variance_geometric (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (coarse fine : ℕ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, IGSIII34.Probability.finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)^2) ≤ secondMoment)
    (inverseMomentBound : IGSIII34.Probability.finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    ‖markedObservableLp rule p positive lessOne fixedPoint (coarse + fine + 1) address true
        (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p) -
      markedObservableLp rule p positive lessOne fixedPoint coarse address true
        (electricalBlockConditionalMean rule p coarse fine)‖ ^ 2 ≤
      (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power)) *
        (((rule.edges : ℝ) ^ (1 / power)) / deriv rule.network.reliability p) ^ (coarse + 1) := by
  rw [marked_electrical_prefix_residual_norm_sq]
  exact generation_block_electrical_residual_variance_geometric rule classical p positive lessOne fixedPoint coarse fine
    powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
    secondMomentBound inverseMomentBound


end
end IGSIII34.Percolation
