import IGSIII.Chemical.SmallBall.ChemicalOmegaMoments
import IGSIII.Chemical.SmallBall.ChemicalOmegaComparison
import IGSIII.Chemical.StationaryField
import IGSIII.Probability.CompactInvariantCore
import IGSIII.Probability.NormalizePositiveFixedPoint
import IGSIII.Probability.LpComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal

theorem exists_positive_chemical_fixed_of_omega_comparison
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (comparisonConstant : ℝ) (comparisonPositive : 0 < comparisonConstant)
    (comparison : ∀ first ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
      ∀ second ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
        first ≤ comparisonConstant • second) :
    ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
      normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
      (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
      ∃ base ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ lower • base ≤ value ∧ value ≤ upper • base := by
  obtain ⟨nonempty, compact, forward, onto⟩ := chemicalOmegaSet_properties rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds
  obtain ⟨core, countable, coreNonempty, subset, coreForward, coreOnto⟩ :=
    exists_countable_invariant_subset
      (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)
      (chemicalOmegaSet rule p positive belowOne fixedPoint growth) nonempty compact forward onto
  have homogeneous := fun scalar scalarNonnegative value =>
    normalizedChemicalTransferLp_smul rule p positive belowOne fixedPoint 2 growth scalar scalarNonnegative value
  obtain ⟨fixed, fixedIdentity, fixedPositive, base, baseMember, lowerBound, upperBound⟩ :=
    exists_positive_fixed_point_of_countable_invariant_family
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)
      (normalizedChemicalTransferLp_continuous rule p positive belowOne fixedPoint 2 growth)
      (normalizedChemicalTransferLp_monotone rule p positive belowOne fixedPoint 2 growth growthPositive.le)
      homogeneous core countable coreNonempty coreForward coreOnto comparisonConstant comparisonPositive
      (fun first firstMember second secondMember => comparison first (subset firstMember) second (subset secondMember))
      (fun value member => chemicalOmega_ae_positive rule classical p positive belowOne fixedPoint
        constant growth growthPositive growthBounds value (subset member))
  obtain ⟨value, valueFixed, valuePositive, valueMeanOne, valueFormula⟩ :=
    exists_mean_one_fixed_of_positive_fixed
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)
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

theorem exists_actual_positive_endogenous_chemical_field
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
        (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
          ∀ address,
            (edgePathFamily rule.network (marks (address, true))).shortest
              (fun edge => chemicalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks) =
                growth * chemicalField rule p positive belowOne fixedPoint value address marks) ∧
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
          ∀ member ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
            lower • value ≤ member ∧ member ≤ upper • value := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds⟩ :=
    exists_actual_chemical_growth rule classical p positive belowOne fixedPoint
  have growthPositive : 0 < growth :=
    lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt classical.scale) growthLower
  obtain ⟨comparisonConstant, comparisonAtLeastOne, comparisonAe⟩ :=
    exists_uniform_chemicalOmega_pairwise_comparison rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds
  have comparisonPositive : 0 < comparisonConstant := zero_lt_one.trans_le comparisonAtLeastOne
  have comparison : ∀ first ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
      ∀ second ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
        first ≤ comparisonConstant • second := by
    intro first firstMember second secondMember
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [comparisonAe first firstMember second secondMember,
      Lp.coeFn_smul comparisonConstant second] with marks inequality scalarEquality
    simpa only [scalarEquality, Pi.smul_apply, smul_eq_mul] using inequality
  obtain ⟨value, valueFixed, valuePositive, valueMeanOne, base, baseMember,
      lower, upper, lowerPositive, upperPositive, lowerBound, upperBound⟩ :=
    exists_positive_chemical_fixed_of_omega_comparison rule classical p positive belowOne fixedPoint
      constant growth growthPositive growthBounds comparisonConstant comparisonPositive comparison
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    value, valueFixed, valuePositive, valueMeanOne,
    chemicalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive value valueFixed,
    (upper * comparisonConstant)⁻¹, comparisonConstant * lower⁻¹,
    inv_pos.mpr (mul_pos upperPositive comparisonPositive),
    mul_pos comparisonPositive (inv_pos.mpr lowerPositive), ?_⟩
  exact lp_family_comparison_with_bounded_base _ comparisonConstant comparisonPositive comparison
    base baseMember value lower upper lowerPositive upperPositive lowerBound upperBound

end IGSIII.Chemical.Substitution
