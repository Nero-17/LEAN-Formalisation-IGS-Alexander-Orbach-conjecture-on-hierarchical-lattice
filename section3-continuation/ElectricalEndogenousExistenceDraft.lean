import IGSIII34.Percolation.ElectricalStationaryField
import IGSIII34.Percolation.ElectricalOmegaPositivity
import IGSIII34.Percolation.ElectricalOmegaComparison
import IGSIII.Probability.CompactInvariantCore
import IGSIII.Probability.NormalizePositiveFixedPoint
import IGSIII.Probability.LpComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal

theorem exists_positive_electrical_fixed_of_omega_comparison
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (comparisonConstant : ℝ) (comparisonPositive : 0 < comparisonConstant)
    (comparison : ∀ first ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
      ∀ second ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
        first ≤ comparisonConstant • second) :
    ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
      normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
      (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
      ∃ base ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ lower • base ≤ value ∧ value ≤ upper • base := by
  obtain ⟨nonempty, compact, forward, onto⟩ := electricalOmegaSet_properties rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds
  obtain ⟨core, countable, coreNonempty, subset, coreForward, coreOnto⟩ :=
    exists_countable_invariant_subset
      (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)
      (electricalOmegaSet rule p positive belowOne fixedPoint growth) nonempty compact forward onto
  have homogeneous := fun scalar scalarNonnegative value =>
    normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 growth scalar scalarNonnegative value
  obtain ⟨fixed, fixedIdentity, fixedPositive, base, baseMember, lowerBound, upperBound⟩ :=
    exists_positive_fixed_point_of_countable_invariant_family
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)
      (normalizedElectricalTransferLp_continuous rule p positive belowOne fixedPoint 2 growth)
      (normalizedElectricalTransferLp_monotone rule p positive belowOne fixedPoint 2 growth growthPositive.le)
      homogeneous core countable coreNonempty coreForward coreOnto comparisonConstant comparisonPositive
      (fun first firstMember second secondMember => comparison first (subset firstMember) second (subset secondMember))
      (fun value member => electricalOmega_ae_positive rule classical p positive belowOne fixedPoint
        growth growthPositive (fun depth => (growthBounds depth).1) value (subset member))
  obtain ⟨value, valueFixed, valuePositive, valueMeanOne, valueFormula⟩ :=
    exists_mean_one_fixed_of_positive_fixed
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)
      homogeneous fixed fixedIdentity fixedPositive
  have fixedMeanPositive := lp2_integral_positive
    (independentInnovationLaw rule p positive belowOne fixedPoint) fixed fixedPositive
  refine ⟨value, valueFixed, valuePositive, valueMeanOne, base, subset baseMember,
    (∫ marks, fixed marks ∂independentInnovationLaw rule p positive belowOne fixedPoint)⁻¹ *
      (comparisonConstant⁻¹ * comparisonConstant⁻¹),
    (∫ marks, fixed marks ∂independentInnovationLaw rule p positive belowOne fixedPoint)⁻¹,
    mul_pos (inv_pos.mpr fixedMeanPositive)
      (mul_pos (inv_pos.mpr comparisonPositive) (inv_pos.mpr comparisonPositive)),
    inv_pos.mpr fixedMeanPositive, ?_, ?_⟩
  · rw [valueFormula, ← smul_smul]
    exact lp_smul_mono lowerBound _ (inv_nonneg.mpr fixedMeanPositive.le)
  · rw [valueFormula]
    exact lp_smul_mono upperBound _ (inv_nonneg.mpr fixedMeanPositive.le)

theorem exists_actual_positive_endogenous_electrical_fixed
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      deriv rule.network.reliability p ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
      (∀ depth, growth ^ depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth) ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
        (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
          ∀ member ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
            lower • value ≤ member ∧ member ≤ upper • value := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds⟩ :=
    exists_actual_electrical_growth rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthPositive : 0 < growth :=
    (zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
      p positive belowOne fixedPoint classical.scale)).trans_le growthLower
  obtain ⟨comparisonConstant, comparisonAtLeastOne, comparison⟩ :=
    exists_uniform_electricalOmega_pairwise_comparison rule classical p positive belowOne fixedPoint
      constant growth growthPositive growthBounds constantPositive
  have comparisonPositive : 0 < comparisonConstant := zero_lt_one.trans_le comparisonAtLeastOne
  obtain ⟨value, valueFixed, valuePositive, valueMeanOne, base, baseMember,
      lower, upper, lowerPositive, upperPositive, lowerBound, upperBound⟩ :=
    exists_positive_electrical_fixed_of_omega_comparison rule classical p positive belowOne fixedPoint
      constant growth growthPositive growthBounds comparisonConstant comparisonPositive comparison
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    value, valueFixed, valuePositive, valueMeanOne,
    (upper * comparisonConstant)⁻¹, comparisonConstant * lower⁻¹,
    inv_pos.mpr (mul_pos upperPositive comparisonPositive),
    mul_pos comparisonPositive (inv_pos.mpr lowerPositive), ?_⟩
  exact lp_family_comparison_with_bounded_base _ comparisonConstant comparisonPositive comparison
    base baseMember value lower upper lowerPositive upperPositive lowerBound upperBound


theorem exists_actual_positive_endogenous_electrical_field
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      deriv rule.network.reliability p ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
      (∀ depth, growth ^ depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth) ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
        (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
          ∀ address, 0 < electricalField rule p positive belowOne fixedPoint value address marks) ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
          ∀ address, electricalCell rule.network (marks (address, true))
            (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) =
              growth*electricalField rule p positive belowOne fixedPoint value address marks) ∧
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
          ∀ member ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
            lower • value ≤ member ∧ member ≤ upper • value := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    value, valueFixed, valuePositive, valueMeanOne, lower, upper, lowerPositive, upperPositive, familyBounds⟩ :=
      exists_actual_positive_endogenous_electrical_fixed rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthPositive := (zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
    p positive belowOne fixedPoint classical.scale)).trans_le growthLower
  exact ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    value, valueFixed, valuePositive, valueMeanOne,
    electricalField_positive rule p positive belowOne fixedPoint value valuePositive,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive value valuePositive valueFixed,
    lower, upper, lowerPositive, upperPositive, familyBounds⟩


end
end IGSIII34.Percolation
