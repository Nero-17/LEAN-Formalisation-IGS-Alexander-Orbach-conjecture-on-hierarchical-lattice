import IGSIII34.Percolation.ElectricalEndogenousExistence
import IGSIII34.Percolation.ElectricalOmegaMoments
import IGSIII.Probability.PositiveSandwichMoments
import IGSIII34.Probability.AllRealMoments

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal

theorem electricalField_natural_moments_of_omega_sandwich
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (familyBounds : ∀ member ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
      lower • value ≤ member ∧ member ≤ upper • value) (power : ℕ) :
    (∫⁻ marks, ENNReal.ofReal (value marks)^power ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞ ∧
    (∫⁻ marks, (ENNReal.ofReal (value marks))⁻¹^power ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞ := by
  obtain ⟨base, baseMember⟩ := (electricalOmegaSet_properties rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds).1
  have valueUpper := lp_le_inv_smul_of_smul_le lower lowerPositive (familyBounds base baseMember).1
  have valueLower := lp_inv_smul_le_of_le_smul upper upperPositive (familyBounds base baseMember).2
  have upperAe : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      value marks ≤ lower⁻¹*base marks := by
    filter_upwards [(Lp.coeFn_le _ _).mpr valueUpper, Lp.coeFn_smul lower⁻¹ base] with marks inequality equality
    simpa only [equality, Pi.smul_apply, smul_eq_mul] using inequality
  have lowerAe : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      upper⁻¹*base marks ≤ value marks := by
    filter_upwards [(Lp.coeFn_le _ _).mpr valueLower, Lp.coeFn_smul upper⁻¹ base] with marks inequality equality
    simpa only [equality, Pi.smul_apply, smul_eq_mul] using inequality
  obtain ⟨positiveBound, positiveFinite, positiveBounds⟩ := electricalOmega_uniform_positive_moment rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive (fun depth => (growthBounds depth).2) power
  obtain ⟨inverseBound, inverseFinite, inverseBounds⟩ := electricalOmega_uniform_inverse_moment rule classical p positive belowOne fixedPoint
    growth growthPositive (fun depth => (growthBounds depth).1) power
  constructor
  · have comparison := lintegral_positive_power_le_of_sandwich (independentInnovationLaw rule p positive belowOne fixedPoint)
      value base lower⁻¹ (inv_nonneg.mpr lowerPositive.le) upperAe power
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) positiveFinite)
    exact comparison.trans (mul_le_mul_left' (positiveBounds base baseMember) _)
  · have comparison := lintegral_inverse_power_le_of_sandwich (independentInnovationLaw rule p positive belowOne fixedPoint)
      value base upper⁻¹ (inv_pos.mpr upperPositive) lowerAe power
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (inv_pos.mpr upperPositive)).ne')) inverseFinite)
    exact comparison.trans (mul_le_mul_left' (inverseBounds base baseMember) _)

theorem electricalField_all_real_moments_of_omega_sandwich
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (familyBounds : ∀ member ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
      lower • value ≤ member ∧ member ≤ upper • value) (exponent : ℝ) :
    Integrable (fun marks => (value marks)^exponent) (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have moments := electricalField_natural_moments_of_omega_sandwich rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive growthBounds value lower upper lowerPositive upperPositive familyBounds
  exact IGSIII34.Probability.integrable_real_power_of_all_natural_moments
    (independentInnovationLaw rule p positive belowOne fixedPoint) value (Lp.stronglyMeasurable value).measurable valuePositive
    (fun power => (moments power).1) (fun power => (moments power).2) exponent

theorem exists_actual_positive_endogenous_electrical_field_all_real_moments
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
        (∀ exponent : ℝ, Integrable (fun marks => (value marks)^exponent)
          (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
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
    value, valueFixed, valuePositive, valueMeanOne, fieldPositive, fieldStationary,
    lower, upper, lowerPositive, upperPositive, familyBounds⟩ :=
      exists_actual_positive_endogenous_electrical_field rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthPositive := (zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
    p positive belowOne fixedPoint classical.scale)).trans_le growthLower
  exact ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    value, valueFixed, valuePositive, valueMeanOne,
    electricalField_all_real_moments_of_omega_sandwich rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds value valuePositive lower upper lowerPositive upperPositive familyBounds,
    fieldPositive, fieldStationary, lower, upper, lowerPositive, upperPositive, familyBounds⟩

end
end IGSIII34.Percolation

