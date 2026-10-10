import IGSIII.Chemical.EndogenousExistence
import IGSIII.Chemical.OmegaPositiveMoments
import IGSIII.Probability.PositiveSandwichMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality MeasureTheory
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal

theorem chemical_value_moments_of_omega_sandwich
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value base : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (baseMember : base ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (lowerBound : lower • base ≤ value) (upperBound : value ≤ upper • base) :
    (∀ power : ℕ, (∫⁻ marks, ENNReal.ofReal (value marks) ^ power
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞) ∧
    (∀ power : ℕ, (∫⁻ marks, (ENNReal.ofReal (value marks))⁻¹ ^ power
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞) ∧
    (∀ parameter : ℝ, 0 ≤ parameter →
      (∫⁻ marks, ENNReal.ofReal (Real.exp (parameter * value marks))
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞) := by
  have upperAe : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      value marks ≤ upper * base marks := by
    filter_upwards [(Lp.coeFn_le _ _).mpr upperBound, Lp.coeFn_smul upper base]
      with marks inequality equality
    simpa only [equality, Pi.smul_apply, smul_eq_mul] using inequality
  have lowerAe : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      lower * base marks ≤ value marks := by
    filter_upwards [(Lp.coeFn_le _ _).mpr lowerBound, Lp.coeFn_smul lower base]
      with marks inequality equality
    simpa only [equality, Pi.smul_apply, smul_eq_mul] using inequality
  constructor
  · intro power
    obtain ⟨bound, valid⟩ := exists_uniform_chemicalOmega_positive_moment rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive meanBounds power
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
    exact (lintegral_positive_power_le_of_sandwich _ value base upper upperPositive.le upperAe power).trans
      (mul_le_mul_left' (valid base baseMember) _)
  constructor
  · intro power
    obtain ⟨bound, valid⟩ := exists_uniform_chemicalOmega_inverse_moment rule classical p positive belowOne fixedPoint
      constant growth growthPositive meanBounds power
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr lowerPositive).ne')) ENNReal.ofReal_ne_top)
    exact (lintegral_inverse_power_le_of_sandwich _ value base lower lowerPositive lowerAe power).trans
      (mul_le_mul_left' (valid base baseMember) _)
  · intro parameter parameterNonnegative
    obtain ⟨bound, valid⟩ := exists_uniform_chemicalOmega_exponential_moment rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive meanBounds (parameter * upper)
      (mul_nonneg parameterNonnegative upperPositive.le)
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (lintegral_exponential_le_of_sandwich _ value base upper parameter parameterNonnegative upperAe).trans
      (valid base baseMember)

theorem chemical_value_all_finite_lp_of_omega_comparison_bounds
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (comparison : ∀ member ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
      lower • value ≤ member ∧ member ≤ upper • value) :
    (∀ order : ℝ≥0∞, order ≠ 0 → order ≠ ∞ →
      MemLp value order (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      MemLp (fun marks => (value marks)⁻¹) order (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
    (∀ parameter : ℝ, 0 ≤ parameter →
      (∫⁻ marks, ENNReal.ofReal (Real.exp (parameter * value marks))
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞) := by
  obtain ⟨nonempty, _⟩ := chemicalOmegaSet_properties rule classical p positive belowOne fixedPoint
    constant growth growthPositive meanBounds
  obtain ⟨base, baseMember⟩ := nonempty
  have baseBounds := comparison base baseMember
  have valueBounds := chemical_value_moments_of_omega_sandwich rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive meanBounds value base baseMember
    upper⁻¹ lower⁻¹ (inv_pos.mpr upperPositive) (inv_pos.mpr lowerPositive)
    (lp_inv_smul_le_of_le_smul upper upperPositive baseBounds.2)
    (lp_le_inv_smul_of_smul_le lower lowerPositive baseBounds.1)
  refine ⟨fun order orderPositive orderFinite => ⟨?_, ?_⟩, valueBounds.2.2⟩
  · exact memLp_of_all_positive_natural_moments _ value (Lp.stronglyMeasurable value).measurable
      (valuePositive.mono (fun _ positivity => positivity.le)) valueBounds.1 order orderPositive orderFinite
  · apply memLp_of_all_positive_natural_moments _ (fun marks => (value marks)⁻¹)
      (Lp.stronglyMeasurable value).measurable.inv
      (valuePositive.mono (fun _ positivity => inv_nonneg.mpr positivity.le)) _ order orderPositive orderFinite
    intro power
    have equality : (∫⁻ marks, ENNReal.ofReal ((value marks)⁻¹) ^ power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
        ∫⁻ marks, (ENNReal.ofReal (value marks))⁻¹ ^ power
          ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
      apply lintegral_congr_ae
      filter_upwards [valuePositive] with marks positivity
      rw [ENNReal.ofReal_inv_of_pos positivity]
    rw [equality]
    exact valueBounds.2.1 power

end IGSIII.Chemical.Substitution
