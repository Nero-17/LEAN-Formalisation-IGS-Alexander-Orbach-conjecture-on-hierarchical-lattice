import IGSIII34.Percolation.InverseEigenlaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped NNReal ENNReal

theorem integrable_nnreal_power_of_lintegral_finite (law : ProbabilityMeasure ℝ≥0) (power : ℕ)
    (finite : (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) < ∞) :
    Integrable (fun value : ℝ≥0 => (value : ℝ) ^ power) (law : Measure ℝ≥0) := by
  have result := integrable_toReal_of_lintegral_ne_top
    (measurable_id.coe_nnreal_ennreal.pow_const power).aemeasurable finite.ne
  simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, id_eq] using result

theorem electrical_eigenlaw_all_real_moments (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1)
    (naturalMoments : ∀ power : ℕ, (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) < ∞)
    (meanAboveOne : 1 < electricalOutputMean rule parameter positive belowOne fixedPoint law)
    (eigenlaw : normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law)
    (almostPositive : ∀ᵐ value ∂(law : Measure ℝ≥0), 0 < value) (exponent : ℝ) :
    Integrable (fun value : ℝ≥0 => (value : ℝ) ^ exponent) (law : Measure ℝ≥0) := by
  by_cases nonnegative : 0 ≤ exponent
  · exact integrable_rpow_of_nat_moments (law : Measure ℝ≥0) NNReal.continuous_coe.measurable
      (fun value => value.2)
      (fun power => integrable_nnreal_power_of_lintegral_finite law power (naturalMoments power)) nonnegative
  · have inverseIntegrable := integrable_rpow_of_nat_moments (law : Measure ℝ≥0)
      NNReal.continuous_coe.measurable.inv (fun value => inv_nonneg.mpr value.2)
      (normalized_electrical_eigenlaw_inverse_moments rule classical parameter positive belowOne fixedPoint
        law meanOne meanAboveOne eigenlaw almostPositive) (neg_nonneg.mpr (le_of_not_ge nonnegative))
    convert inverseIntegrable using 1
    funext value
    change (value : ℝ) ^ exponent = ((value : ℝ)⁻¹) ^ (-exponent)
    rw [← Real.rpow_neg_eq_inv_rpow, neg_neg]

theorem exists_electrical_eigenlaw_all_real_moments (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ law : ProbabilityMeasure ℝ≥0,
      (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1 ∧
      (∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value : ℝ) ^ exponent) (law : Measure ℝ≥0)) ∧
      normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law ∧
      1 < electricalOutputMean rule parameter positive belowOne fixedPoint law ∧
      ∀ᵐ value ∂(law : Measure ℝ≥0), 0 < value := by
  obtain ⟨law, meanOne, moments, fixed, meanAboveOne, almostPositive⟩ :=
    exists_positive_electrical_eigenlaw rule classical parameter positive belowOne fixedPoint
  exact ⟨law, meanOne, electrical_eigenlaw_all_real_moments rule classical parameter positive belowOne fixedPoint
    law meanOne moments meanAboveOne fixed almostPositive, fixed, meanAboveOne, almostPositive⟩

end
end IGSIII34.Percolation
