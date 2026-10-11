import IGSIII4.AlexanderOrbach
import IGSIII4.CriticalSupersolution

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34 MeasureTheory

/-- Conclusions of Section 4 for the actual Section 2 chemical scalar and
the Section 3 electrical scalar. Every field is proved below. -/
structure SectionFourConclusions (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) : Prop where
  strictResistance : 1 < accepted.growth ∧ accepted.growth < chemical.growth
  coreBelowFullMass : terminalCoreMean rule.network probability < actualMassGrowth rule probability
  coreGrowthClock : chemical.growth ^ 2 ≤ terminalCoreMean rule.network probability * accepted.growth
  strictGrowthClock : chemical.growth ^ 2 < actualMassGrowth rule probability * accepted.growth
  dimensionComparisons : 0 < chemicalResistanceDimension accepted.growth chemical.growth ∧
    chemicalResistanceDimension accepted.growth chemical.growth < 1 ∧
    2 < chemicalMassDimension (actualMassGrowth rule probability) chemical.growth +
      chemicalResistanceDimension accepted.growth chemical.growth
  aoMassEquality : typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth = (4 / 3 : ℝ) ↔
    actualMassGrowth rule probability = accepted.growth ^ 2
  aoDimensionEquality : typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth = (4 / 3 : ℝ) ↔
    chemicalMassDimension (actualMassGrowth rule probability) chemical.growth =
      2 * chemicalResistanceDimension accepted.growth chemical.growth
  aoRegion : ¬ ((4 / 3 : ℝ) < chemicalMassDimension (actualMassGrowth rule probability) chemical.growth ∧
    chemicalMassDimension (actualMassGrowth rule probability) chemical.growth < 2 ∧
    (2 / 3 : ℝ) < chemicalResistanceDimension accepted.growth chemical.growth ∧
    chemicalResistanceDimension accepted.growth chemical.growth < 1) →
    typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth ≠ (4 / 3 : ℝ)
  largeMassSign : 2 ≤ chemicalMassDimension (actualMassGrowth rule probability) chemical.growth →
    (4 / 3 : ℝ) < typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth
  smallMassSign : chemicalMassDimension (actualMassGrowth rule probability) chemical.growth ≤ (4 / 3 : ℝ) →
    typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth < (4 / 3 : ℝ)

theorem section_four_for_actual_chemical_scalar (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    SectionFourConclusions rule probability positive belowOne fixedPoint accepted chemical where
  strictResistance := actual_strict_chemical_resistance rule classicalRule probability positive belowOne fixedPoint accepted chemical
  coreBelowFullMass := terminalCoreMean_strictly_below_mass_radius classicalRule positive belowOne
  coreGrowthClock := actual_core_growth_clock rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical
  strictGrowthClock := actual_strict_growth_clock rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical
  dimensionComparisons := actual_dimension_comparisons rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical
  aoMassEquality := (actual_ao_equalities rule classicalRule probability positive belowOne fixedPoint accepted chemical).1
  aoDimensionEquality := (actual_ao_equalities rule classicalRule probability positive belowOne fixedPoint accepted chemical).2
  aoRegion := actual_ao_region rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical
  largeMassSign := actual_spectral_above_ao_of_mass_at_least_two rule classicalRule probability positive belowOne fixedPoint accepted chemical
  smallMassSign := actual_spectral_below_ao_of_mass_at_most_four_thirds rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical

theorem exists_actual_section_four (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule) :
    ∃ chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint,
      SectionFourConclusions rule probability positive belowOne fixedPoint accepted chemical := by
  obtain ⟨chemical⟩ := exists_actual_chemical_section_two rule classicalRule probability positive belowOne fixedPoint
  exact ⟨chemical, section_four_for_actual_chemical_scalar rule classicalRule probability positive belowOne fixedPoint
    accepted upper pruning chemical⟩

/-- Apply Section 3's accepted typical-point spectral formula, including its
outer probability-one event and inner almost-everywhere speed measure. -/
theorem typical_point_ao_region {Sample Point : Type*} [MeasurableSpace Sample] [MeasurableSpace Point]
    (sampleLaw : Measure Sample) (speedMeasure : Sample → Measure Point)
    (spectralValue : Sample → Point → ℝ)
    (rule : Rule) (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint)
    (conclusions : SectionFourConclusions rule probability positive belowOne fixedPoint accepted chemical)
    (acceptedSectionThreeFormula : ∀ᵐ sample ∂sampleLaw, ∀ᵐ point ∂speedMeasure sample,
      spectralValue sample point = typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth)
    (outside : ¬ ((4 / 3 : ℝ) < chemicalMassDimension (actualMassGrowth rule probability) chemical.growth ∧
      chemicalMassDimension (actualMassGrowth rule probability) chemical.growth < 2 ∧
      (2 / 3 : ℝ) < chemicalResistanceDimension accepted.growth chemical.growth ∧
      chemicalResistanceDimension accepted.growth chemical.growth < 1)) :
    ∀ᵐ sample ∂sampleLaw, ∀ᵐ point ∂speedMeasure sample, spectralValue sample point ≠ (4 / 3 : ℝ) := by
  filter_upwards [acceptedSectionThreeFormula] with sample formula
  filter_upwards [formula] with point identity
  rw [identity]
  exact conclusions.aoRegion outside

end
end IGSIII4
