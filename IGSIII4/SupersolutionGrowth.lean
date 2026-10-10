import IGSIII4.SupersolutionConditionalBound
import IGSIII4.AcceptedSectionThree
import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII34.Percolation
open scoped NNReal

theorem supersolution_growth_lower_bound_positive_input (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) (valuePositive : ∀ marks, 0 < (value marks : ℝ))
    (integrable : Integrable (fun marks => (value marks : ℝ))
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseIntegrable : Integrable (fun marks => (value marks : ℝ)⁻¹)
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseMeanPositive : 0 < ∫ marks, (value marks : ℝ)⁻¹
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    {factor : ℝ} (factorPositive : 0 < factor)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule (fun marks => (value marks : ℝ)) marks ≤ factor * (value marks : ℝ)) :
    accepted.growth ≤ factor := by
  have powerBound (depth : ℕ) : accepted.growth ^ (depth + 1) ≤ factor ^ (depth + 1) *
      ((∫ marks, (value marks : ℝ)⁻¹ ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
        ∫ marks, (value marks : ℝ) ∂independentInnovationLaw rule probability positive belowOne fixedPoint) := by
    have conditionalBound := supersolution_conditional_bound rule probability positive belowOne fixedPoint
      value measurable valuePositive integrable inverseIntegrable inverseMeanPositive factorPositive supersolution depth
    have resistanceMeasurable : Measurable (fun marks => unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)) :=
      electricalCell_measurable (rule.generation depth).network _
        (markedGenerationConfiguration_measurable rule depth [] true)
        (fun _ _ => 1) measurable_const (fun _ _ => zero_le_one)
    have resistanceNonnegative (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
        0 ≤ unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true) :=
      (IGSIII34.Percolation.network (rule.generation depth).network _).effectiveResistance_nonnegative_all
        (fun _ => zero_le_one)
    have upperIntegrable : Integrable (fun marks => factor ^ (depth + 1) *
        (∫ other, (value other : ℝ)⁻¹ ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
        (condExp (innovationFiltration rule (depth + 1))
          (independentInnovationLaw rule probability positive belowOne fixedPoint)
          (fun marks => (value marks : ℝ))) marks)
        (independentInnovationLaw rule probability positive belowOne fixedPoint) :=
      integrable_condExp.const_mul _
    have resistanceIntegrable : Integrable (fun marks => unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true))
        (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
      apply upperIntegrable.mono' resistanceMeasurable.aestronglyMeasurable
      filter_upwards [conditionalBound] with marks bound
      rw [Real.norm_eq_abs, abs_of_nonneg (resistanceNonnegative marks)]
      exact bound
    have integralBound := integral_mono_ae resistanceIntegrable upperIntegrable conditionalBound
    rw [integral_const_mul, integral_condExp ((innovationFiltration rule).le (depth + 1))] at integralBound
    exact (accepted.meanLower depth).trans (by simpa only [mul_assoc] using integralBound)
  by_contra lowerFails
  have strictlySmaller : factor < accepted.growth := lt_of_not_ge lowerFails
  have ratioAboveOne : 1 < accepted.growth / factor := (one_lt_div factorPositive).mpr strictlySmaller
  have ratioBound (depth : ℕ) : (accepted.growth / factor) ^ (depth + 1) ≤
      (∫ marks, (value marks : ℝ)⁻¹ ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
        ∫ marks, (value marks : ℝ) ∂independentInnovationLaw rule probability positive belowOne fixedPoint := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos factorPositive _)).mpr (by simpa only [mul_comm] using powerBound depth)
  obtain ⟨depth, tooLarge⟩ := pow_unbounded_of_one_lt
    (max (1 : ℝ) ((∫ marks, (value marks : ℝ)⁻¹
        ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
      ∫ marks, (value marks : ℝ) ∂independentInnovationLaw rule probability positive belowOne fixedPoint)) ratioAboveOne
  have powerIncreases : (accepted.growth / factor) ^ depth ≤ (accepted.growth / factor) ^ (depth + 1) := by
    rw [pow_succ]
    nlinarith only [pow_nonneg (zero_lt_one.trans ratioAboveOne).le depth, ratioAboveOne]
  exact (not_lt_of_ge ((powerIncreases.trans (ratioBound depth)).trans (le_max_right _ _))) tooLarge

end
end IGSIII4
