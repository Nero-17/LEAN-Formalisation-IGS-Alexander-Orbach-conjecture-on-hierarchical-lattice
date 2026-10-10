import IGSIII34.Percolation.ElectricalBlockOrdering
import IGSIII34.Percolation.ResistancePrefixL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal

theorem markedGrowthScaledResistance_eq_mean_scaled
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ) (address : List (Fin rule.edges)) :
    markedObservableLp rule p positive belowOne fixedPoint depth address true (growthScaledResistance rule growth depth) =
      (conditionalMeanResistance (rule.generation depth).network p / growth^(depth+1)) •
        markedObservableLp rule p positive belowOne fixedPoint depth address true
          (normalizedConfigurationResistance (rule.generation depth).network p) := by
  have meanPositive := generation_conditionalMeanResistance_positive rule classical p positive belowOne fixedPoint depth
  rw [← markedObservableLp_scale]
  congr 1
  funext configuration
  unfold growthScaledResistance normalizedConfigurationResistance
  field_simp

theorem markedElectricalBlockMean_eq_parent_scale
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (coarse fine : ℕ) (address : List (Fin rule.edges)) :
    markedObservableLp rule p positive belowOne fixedPoint coarse address true
        (generationElectricalBlockMean rule p growth coarse fine) =
      (conditionalMeanResistance (rule.generation (coarse+fine+1)).network p / growth^(coarse+fine+2)) •
        markedObservableLp rule p positive belowOne fixedPoint coarse address true
          (electricalBlockConditionalMean rule p coarse fine) := by
  rw [← markedObservableLp_scale]
  congr 1
  funext configuration
  exact generationElectricalBlockMean_eq_parent_scale rule classical p positive belowOne fixedPoint growth coarse fine configuration

theorem marked_growth_electrical_residual_geometric
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (address : List (Fin rule.edges)) (coarse fine : ℕ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, IGSIII34.Probability.finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)^2) ≤ secondMoment)
    (inverseMomentBound : IGSIII34.Probability.finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation fine).network p configuration)⁻¹^power) ≤ inverseMoment) :
    ‖markedObservableLp rule p positive belowOne fixedPoint (coarse+fine+1) address true
        (growthScaledResistance rule growth (coarse+fine+1)) -
      markedObservableLp rule p positive belowOne fixedPoint coarse address true
        (generationElectricalBlockMean rule p growth coarse fine)‖ ≤
      constant⁻¹*Real.sqrt ((2*secondMoment*Real.sqrt secondMoment*inverseMoment^(1/power))*
        (((rule.edges : ℝ)^(1/power))/deriv rule.network.reliability p)^(coarse+1)) := by
  have parentPositive := generation_conditionalMeanResistance_positive rule classical p positive belowOne fixedPoint (coarse+fine+1)
  have ratioBound := (growthBounds ((coarse+fine+1)+1)).2
  rw [electricalOrbitScale_succ_eq_generation_mean rule classical p positive belowOne fixedPoint] at ratioBound
  have ratioUpper := (div_le_iff₀ (pow_pos growthPositive ((coarse+fine+1)+1))).mpr ratioBound
  rw [markedGrowthScaledResistance_eq_mean_scaled rule classical p positive belowOne fixedPoint growth growthPositive,
    markedElectricalBlockMean_eq_parent_scale rule classical p positive belowOne fixedPoint,
    ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg parentPositive.le (pow_pos growthPositive _).le)]
  exact mul_le_mul ratioUpper
    (Real.le_sqrt_of_sq_le (marked_electrical_prefix_residual_variance_geometric rule classical p positive belowOne fixedPoint
      address coarse fine powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
      secondMomentBound inverseMomentBound))
    (norm_nonneg _) (inv_nonneg.mpr constantPositive.le)

end
end IGSIII34.Percolation
