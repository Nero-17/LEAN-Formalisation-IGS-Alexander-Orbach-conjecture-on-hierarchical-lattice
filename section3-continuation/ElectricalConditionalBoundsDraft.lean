import IGSIII34.Percolation.BlockResistance
import IGSIII34.Percolation.IIDJensen
import IGSIII34.Percolation.MeanGrowthSteps

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork
open IGSIII34.Probability IGSIII.Chemical.Substitution
open scoped BigOperators

def generationElectricalBlockMean (rule : Rule) (p growth : ℝ) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation coarse).edges) : ℝ :=
  (conditionalMeanResistance (rule.generation fine).network p / growth^(coarse+fine+2)) *
    finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
      (rule.generation fine).network.conditionalCellWeight p true)) (fun cells =>
        electricalCell (rule.generation coarse).network configuration
          (fun edge => positiveNormalizedResistance (rule.generation fine).network p (cells edge)))

theorem generationElectricalBlockMean_sandwich
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (inverseMoment : ℝ) (inverseAtLeastOne : 1 ≤ inverseMoment)
    (inverseBound : ∀ depth, finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)⁻¹) ≤ inverseMoment)
    (coarse fine : ℕ) (configuration : Configuration (rule.generation coarse).edges) :
    unitConfigurationResistance (rule.generation coarse).network configuration / growth^(coarse+1) / inverseMoment ≤
      generationElectricalBlockMean rule p growth coarse fine configuration ∧
    generationElectricalBlockMean rule p growth coarse fine configuration ≤
      constant⁻¹*(unitConfigurationResistance (rule.generation coarse).network configuration / growth^(coarse+1)) := by
  have inversePositive := zero_lt_one.trans_le inverseAtLeastOne
  have innerPositive := generation_conditionalMeanResistance_positive rule classical p positive belowOne fixedPoint fine
  by_cases crossing : (rule.generation coarse).network.crosses configuration = true
  · have sandwich := finite_iid_electricalCell_mean_sandwich (rule.generation coarse).network configuration crossing
      ((rule.generation fine).network.conditionalCellWeight p true)
      ((rule.generation fine).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
      ((rule.generation fine).network.sum_conditionalCellWeight p
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]) true)
      (positiveNormalizedResistance (rule.generation fine).network p)
      (positiveNormalizedResistance_positive _ p innerPositive)
      (positiveNormalizedResistance_mean_one _ p innerPositive) inverseMoment (inverseBound fine)
    have meanBounds := growthBounds (fine+1)
    rw [electricalOrbitScale_succ_eq_generation_mean rule classical p positive belowOne fixedPoint] at meanBounds
    have lowerRatio : 1 ≤ conditionalMeanResistance (rule.generation fine).network p / growth^(fine+1) :=
      (le_div_iff₀ (pow_pos growthPositive _)).mpr (by simpa only [one_mul] using meanBounds.1)
    have upperRatio : conditionalMeanResistance (rule.generation fine).network p / growth^(fine+1) ≤ constant⁻¹ :=
      (div_le_iff₀ (pow_pos growthPositive _)).mpr meanBounds.2
    have unitNonnegative : 0 ≤ unitConfigurationResistance (rule.generation coarse).network configuration :=
      (network (rule.generation coarse).network configuration).effectiveResistance_nonnegative_all (fun _ => zero_le_one)
    have meanNonnegative := (div_nonneg unitNonnegative inversePositive.le).trans sandwich.1
    unfold generationElectricalBlockMean
    have factorization : coarse+fine+2 = (coarse+1)+(fine+1) := by omega
    rw [factorization, pow_add growth (coarse+1) (fine+1)]
    constructor
    · calc
        _ = (1 : ℝ)*(unitConfigurationResistance (rule.generation coarse).network configuration / inverseMoment / growth^(coarse+1)) := by ring
        _ ≤ (conditionalMeanResistance (rule.generation fine).network p / growth^(fine+1))*
            (finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
              (rule.generation fine).network.conditionalCellWeight p true)) (fun cells =>
                electricalCell (rule.generation coarse).network configuration
                  (fun edge => positiveNormalizedResistance (rule.generation fine).network p (cells edge))) / growth^(coarse+1)) :=
          mul_le_mul lowerRatio (div_le_div_of_nonneg_right sandwich.1 (pow_pos growthPositive _).le)
            (div_nonneg (div_nonneg unitNonnegative inversePositive.le) (pow_pos growthPositive _).le)
            ((zero_le_one.trans lowerRatio))
        _ = _ := by ring
    · calc
        _ = (conditionalMeanResistance (rule.generation fine).network p / growth^(fine+1))*
            (finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
              (rule.generation fine).network.conditionalCellWeight p true)) (fun cells =>
                electricalCell (rule.generation coarse).network configuration
                  (fun edge => positiveNormalizedResistance (rule.generation fine).network p (cells edge))) / growth^(coarse+1)) := by ring
        _ ≤ _ := mul_le_mul upperRatio
          (div_le_div_of_nonneg_right sandwich.2 (pow_pos growthPositive _).le)
          (div_nonneg meanNonnegative (pow_pos growthPositive _).le)
          ((zero_le_one.trans lowerRatio).trans upperRatio)
  · have zeroCell := electricalCell_eq_zero_of_not_crosses (rule.generation coarse).network configuration crossing
    simp only [generationElectricalBlockMean, zeroCell, unitConfigurationResistance,
      mul_zero, finiteMean, Finset.sum_const_zero, zero_div, le_refl, and_self]

end
end IGSIII34.Percolation
