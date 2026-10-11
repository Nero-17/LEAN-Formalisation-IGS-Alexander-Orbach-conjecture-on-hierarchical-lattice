import IGSIII4.ActualCoreClock
import IGSIII34.AO.Dimension
import Universality.Percolation.MassSpectralLowerBound

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34

def actualMassGrowth (rule : Rule) (probability : ℝ) : ℝ :=
  (spectralRadius ℂ ((rule.network.massMatrix probability).map Complex.ofReal)).toReal

theorem actualMassGrowth_above_one (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1) :
    1 < actualMassGrowth rule probability := by
  obtain ⟨degreeLower, radiusLower, _⟩ := classicalRule.terminal_degree_spectral_bounds probability positive belowOne
  have degreeLowerReal : (2 : ℝ) ≤ (rule.network.fullGraph.degree rule.network.source : ℝ) := by exact_mod_cast degreeLower
  exact (by linarith : (1 : ℝ) < (rule.network.fullGraph.degree rule.network.source : ℝ)).trans radiusLower

theorem actual_chemical_growth_above_one (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    1 < chemical.growth := lt_of_lt_of_le (by exact_mod_cast classicalRule.scale) chemical.growthLower

theorem actual_strict_growth_clock (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    chemical.growth ^ 2 < actualMassGrowth rule probability * accepted.growth :=
  strict_clock_of_core_comparisons (zero_lt_one.trans accepted.growthAboveOne)
    (terminalCoreMean_strictly_below_mass_radius classicalRule positive belowOne)
    (actual_core_growth_clock rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical)

theorem actual_dimension_comparisons (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    0 < chemicalResistanceDimension accepted.growth chemical.growth ∧
      chemicalResistanceDimension accepted.growth chemical.growth < 1 ∧
      2 < chemicalMassDimension (actualMassGrowth rule probability) chemical.growth +
        chemicalResistanceDimension accepted.growth chemical.growth := by
  have chemicalAbove := actual_chemical_growth_above_one rule classicalRule probability positive belowOne fixedPoint chemical
  refine ⟨chemicalResistanceDimension_pos accepted.growthAboveOne chemicalAbove,
    chemicalResistanceDimension_lt_one (zero_lt_one.trans accepted.growthAboveOne) chemicalAbove
      (actual_strict_chemical_resistance rule classicalRule probability positive belowOne fixedPoint accepted chemical).2, ?_⟩
  exact strict_dimension_clock_of_growth_clock
    (zero_lt_one.trans (actualMassGrowth_above_one rule classicalRule probability positive belowOne))
    (zero_lt_one.trans accepted.growthAboveOne) chemicalAbove
    (actual_strict_growth_clock rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical)

theorem actual_ao_equalities (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    (typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth = (4 / 3 : ℝ) ↔
      actualMassGrowth rule probability = accepted.growth ^ 2) ∧
    (typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth = (4 / 3 : ℝ) ↔
      chemicalMassDimension (actualMassGrowth rule probability) chemical.growth =
        2 * chemicalResistanceDimension accepted.growth chemical.growth) := by
  have chemicalAbove := actual_chemical_growth_above_one rule classicalRule probability positive belowOne fixedPoint chemical
  have massAbove := actualMassGrowth_above_one rule classicalRule probability positive belowOne
  refine ⟨typicalSpectralDimension_eq_four_thirds_iff massAbove accepted.growthAboveOne, ?_⟩
  rw [typicalSpectralDimension_eq_dimensionRatio massAbove accepted.growthAboveOne chemicalAbove]
  apply dimensionRatio_eq_four_thirds_iff
  exact add_pos (div_pos (Real.log_pos massAbove) (Real.log_pos chemicalAbove))
    (chemicalResistanceDimension_pos accepted.growthAboveOne chemicalAbove)

theorem actual_ao_equality_forces_open_rectangle (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint)
    (equality : typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth = (4 / 3 : ℝ)) :
    (4 / 3 : ℝ) < chemicalMassDimension (actualMassGrowth rule probability) chemical.growth ∧
      chemicalMassDimension (actualMassGrowth rule probability) chemical.growth < 2 ∧
      (2 / 3 : ℝ) < chemicalResistanceDimension accepted.growth chemical.growth ∧
      chemicalResistanceDimension accepted.growth chemical.growth < 1 := by
  obtain ⟨resistancePositive, resistanceBelow, clock⟩ :=
    actual_dimension_comparisons rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical
  apply ao_equality_forces_open_rectangle resistancePositive resistanceBelow clock
  rwa [← typicalSpectralDimension_eq_dimensionRatio
    (actualMassGrowth_above_one rule classicalRule probability positive belowOne) accepted.growthAboveOne
    (actual_chemical_growth_above_one rule classicalRule probability positive belowOne fixedPoint chemical)]

theorem actual_ao_region (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint)
    (outside : ¬ ((4 / 3 : ℝ) < chemicalMassDimension (actualMassGrowth rule probability) chemical.growth ∧
      chemicalMassDimension (actualMassGrowth rule probability) chemical.growth < 2 ∧
      (2 / 3 : ℝ) < chemicalResistanceDimension accepted.growth chemical.growth ∧
      chemicalResistanceDimension accepted.growth chemical.growth < 1)) :
    typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth ≠ (4 / 3 : ℝ) := by
  intro equality
  exact outside (actual_ao_equality_forces_open_rectangle rule classicalRule probability positive belowOne fixedPoint
    accepted upper pruning chemical equality)

theorem actual_spectral_above_ao_of_mass_at_least_two (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint)
    (largeMass : 2 ≤ chemicalMassDimension (actualMassGrowth rule probability) chemical.growth) :
    (4 / 3 : ℝ) < typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth := by
  have chemicalAbove := actual_chemical_growth_above_one rule classicalRule probability positive belowOne fixedPoint chemical
  rw [typicalSpectralDimension_eq_dimensionRatio (actualMassGrowth_above_one rule classicalRule probability positive belowOne)
    accepted.growthAboveOne chemicalAbove]
  exact spectral_above_ao_of_mass_at_least_two
    (chemicalResistanceDimension_pos accepted.growthAboveOne chemicalAbove)
    (chemicalResistanceDimension_lt_one (zero_lt_one.trans accepted.growthAboveOne) chemicalAbove
      (actual_strict_chemical_resistance rule classicalRule probability positive belowOne fixedPoint accepted chemical).2) largeMass

theorem actual_spectral_below_ao_of_mass_at_most_four_thirds (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint)
    (smallMass : chemicalMassDimension (actualMassGrowth rule probability) chemical.growth ≤ (4 / 3 : ℝ)) :
    typicalSpectralDimension (actualMassGrowth rule probability) accepted.growth < (4 / 3 : ℝ) := by
  rw [typicalSpectralDimension_eq_dimensionRatio (actualMassGrowth_above_one rule classicalRule probability positive belowOne)
    accepted.growthAboveOne (actual_chemical_growth_above_one rule classicalRule probability positive belowOne fixedPoint chemical)]
  exact spectral_below_ao_of_mass_at_most_four_thirds
    (actual_dimension_comparisons rule classicalRule probability positive belowOne fixedPoint accepted upper pruning chemical).2.2 smallMass

/-- Conjecture ao-global is recorded as a predicate only. No proof is claimed. -/
def GlobalAlexanderOrbachConjecture : Prop :=
  ∀ (rule : Rule), rule.Classical → ∀ (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint),
      actualMassGrowth rule probability ≠ accepted.growth ^ 2

end
end IGSIII4
