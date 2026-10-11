import IGSIII4.ActualSectionThreeInputs
import IGSIII4.SectionFour
import IGSIII4.LongDiamond

/-! Section 4 for the actual natural resistance constructed in Section 3.
No accepted electrical field, sandwich, pruning or spectral formula is an
input to these theorems. The global AO assertion remains a conjecture. -/
set_option autoImplicit false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory IGSIII34 IGSIII34.Percolation

theorem section_four_for_natural_resistance
    (rule : Rule) (classicalRule : rule.Classical) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (natural : NaturalResistanceCompletion20261011 rule probability positive belowOne fixedPoint)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    SectionFourConclusions rule probability positive belowOne fixedPoint
      (naturalSectionFourElectrical rule probability positive belowOne fixedPoint natural) chemical :=
  section_four_for_actual_chemical_scalar rule classicalRule probability positive belowOne fixedPoint
    (naturalSectionFourElectrical rule probability positive belowOne fixedPoint natural)
    (naturalSectionFourMeanUpper rule classicalRule probability positive belowOne fixedPoint natural)
    (actual_section_four_core_pruning rule classicalRule) chemical

/-- Both witnesses, and every former Section 3 proof input, are constructed
under the original classical-rule and interior critical-point hypotheses. -/
theorem exists_section_four_from_proved_sections_two_three
    (rule : Rule) (classicalRule : rule.Classical) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) :
    ∃ natural : NaturalResistanceCompletion20261011 rule probability positive belowOne fixedPoint,
    ∃ chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint,
      SectionFourConclusions rule probability positive belowOne fixedPoint
        (naturalSectionFourElectrical rule probability positive belowOne fixedPoint natural) chemical := by
  obtain ⟨natural⟩ := exists_natural_resistance_completion20261011
    rule classicalRule probability positive belowOne fixedPoint
  obtain ⟨chemical⟩ := exists_actual_chemical_section_two
    rule classicalRule probability positive belowOne fixedPoint
  exact ⟨natural, chemical, section_four_for_natural_resistance rule classicalRule probability
    positive belowOne fixedPoint natural chemical⟩

theorem natural_critical_supersolution
    (rule : Rule) (classicalRule : rule.Classical) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (natural : NaturalResistanceCompletion20261011 rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (IGSIII.Chemical.Substitution.independentInnovationLaw
      rule probability positive belowOne fixedPoint))
    (nonnegative : ∀ᵐ marks ∂IGSIII.Chemical.Substitution.independentInnovationLaw
      rule probability positive belowOne fixedPoint, 0 ≤ value marks)
    (meanPositive : 0 < ∫ marks, value marks ∂IGSIII.Chemical.Substitution.independentInnovationLaw
      rule probability positive belowOne fixedPoint)
    {factor : ℝ} (factorPositive : 0 < factor)
    (supersolution : ∀ᵐ marks ∂IGSIII.Chemical.Substitution.independentInnovationLaw
      rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ factor * value marks) :
    natural.growth ≤ factor ∧ (factor = natural.growth →
      ∃ scalar : ℝ, 0 < scalar ∧
        value =ᵐ[IGSIII.Chemical.Substitution.independentInnovationLaw
          rule probability positive belowOne fixedPoint] fun marks => scalar * natural.field marks) :=
  critical_supersolution rule classicalRule probability positive belowOne fixedPoint
    (naturalSectionFourElectrical rule probability positive belowOne fixedPoint natural)
    value measurable integrable nonnegative meanPositive factorPositive supersolution

theorem natural_long_diamond_spectral_dimension_strictly_below_four_thirds
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : LongDiamond.network.reliability probability = probability)
    (natural : NaturalResistanceCompletion20261011 LongDiamond.rule probability positive belowOne fixedPoint) :
    typicalSpectralDimension (actualMassGrowth LongDiamond.rule probability) natural.growth < (4 / 3 : ℝ) :=
  LongDiamond.spectral_dimension_strictly_below_four_thirds probability positive belowOne fixedPoint
    (naturalSectionFourElectrical LongDiamond.rule probability positive belowOne fixedPoint natural)
    (naturalSectionFourMeanUpper LongDiamond.rule LongDiamond.classical probability positive belowOne fixedPoint natural)
    (actual_section_four_core_pruning LongDiamond.rule LongDiamond.classical)

end
end IGSIII4
