import IGSIII34.Percolation.ElectricalConditionalBounds
import IGSIII34.Percolation.GrowthCompactResistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork
open IGSIII34.Probability IGSIII.Chemical.Substitution
open scoped BigOperators

theorem generationElectricalBlockMean_pairwise_le
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (inverseMoment : ℝ) (inverseAtLeastOne : 1 ≤ inverseMoment)
    (inverseBound : ∀ depth, finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)⁻¹) ≤ inverseMoment)
    (constantPositive : 0 < constant) (coarse firstFine secondFine : ℕ)
    (configuration : Configuration (rule.generation coarse).edges) :
    generationElectricalBlockMean rule p growth coarse firstFine configuration ≤
      (inverseMoment*constant⁻¹)*generationElectricalBlockMean rule p growth coarse secondFine configuration := by
  have firstBounds := generationElectricalBlockMean_sandwich rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds inverseMoment inverseAtLeastOne inverseBound coarse firstFine configuration
  have secondBounds := generationElectricalBlockMean_sandwich rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds inverseMoment inverseAtLeastOne inverseBound coarse secondFine configuration
  have inversePositive := zero_lt_one.trans_le inverseAtLeastOne
  calc
    _ ≤ constant⁻¹*(unitConfigurationResistance (rule.generation coarse).network configuration / growth^(coarse+1)) := firstBounds.2
    _ = (inverseMoment*constant⁻¹)*(unitConfigurationResistance (rule.generation coarse).network configuration / growth^(coarse+1) / inverseMoment) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left secondBounds.1
      (mul_nonneg inversePositive.le (inv_nonneg.mpr constantPositive.le))

theorem generationElectricalBlockMean_eq_parent_scale
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (coarse fine : ℕ) (configuration : Configuration (rule.generation coarse).edges) :
    generationElectricalBlockMean rule p growth coarse fine configuration =
      (conditionalMeanResistance (rule.generation (coarse+fine+1)).network p / growth^(coarse+fine+2))*
        electricalBlockConditionalMean rule p coarse fine configuration := by
  have parentPositive := generation_conditionalMeanResistance_positive rule classical p positive belowOne fixedPoint (coarse+fine+1)
  unfold generationElectricalBlockMean electricalBlockConditionalMean
  field_simp

end
end IGSIII34.Percolation
