import IGSIII.Chemical.ChemicalScalar
import IGSIII4.StrictChemicalResistance

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution
open IGSIII.Geometry IGSIII.Chemical.SmallBall
open scoped ENNReal

/-- A small projection of the already proved Section 2 scalar theorem.
Existence below is proved, rather than accepted as a Section 3 dependency. -/
structure ActualChemicalSectionTwo (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) where
  growth : ℝ
  growthLower : (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth
  growthUpper : growth ≤ longestTerminalPath rule.network
  meanBounds : ∃ constant : ℝ, 0 < constant ∧ ∀ depth,
    growth ^ depth ≤ manuscriptDistanceMean rule probability depth ∧
      manuscriptDistanceMean rule probability depth ≤ constant⁻¹ * growth ^ depth
  field : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ
  fieldMeasurable : Measurable field
  fieldIntegrable : Integrable field (independentInnovationLaw rule probability positive belowOne fixedPoint)
  fieldPositive : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 < field marks
  fieldMeanOne : (∫ marks, field marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint) = 1
  fieldEquation : chemicalTransfer rule field
    =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint] fun marks => growth * field marks

theorem exists_actual_chemical_section_two (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) :
    Nonempty (ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) := by
  obtain ⟨constant, growth, constantPositive, _constantAtMostOne, growthLower, growthUpper, meanBounds,
    value, valueFixed, valuePositive, valueMeanOne, _amplitude, _amplitudeAtLeastOne, _rest⟩ :=
    exists_actual_chemical_scalar rule classicalRule probability positive belowOne fixedPoint
  have growthPositive : 0 < growth := lt_of_lt_of_le
    (by exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale) growthLower
  have equation : chemicalTransfer rule value
      =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint] fun marks => growth * value marks := by
    filter_upwards [chemicalField_stationary_of_fixed rule probability positive belowOne fixedPoint
      growth growthPositive value valueFixed] with marks stationary
    have emptyShift : IGSIII.Probability.innovationTreeShift rule [] marks = marks := by
      funext coordinate
      simp [IGSIII.Probability.innovationTreeShift]
    simpa only [chemicalTransfer, chemicalField, emptyShift,
      List.nil_append, List.append_nil] using stationary []
  exact ⟨⟨growth, growthLower, growthUpper, ⟨constant, constantPositive, meanBounds⟩,
    value, (Lp.stronglyMeasurable value).measurable, (Lp.memLp value).integrable (by norm_num),
    valuePositive, valueMeanOne, equation⟩⟩

theorem actual_strict_chemical_resistance (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    1 < accepted.growth ∧ accepted.growth < chemical.growth := by
  have growthPositive : 0 < chemical.growth := lt_of_lt_of_le
    (by exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale) chemical.growthLower
  apply strict_chemical_resistance_of_eigenfunction rule classicalRule probability positive belowOne fixedPoint accepted
    chemical.field chemical.fieldMeasurable chemical.fieldIntegrable chemical.fieldPositive
  · rw [chemical.fieldMeanOne]
    exact zero_lt_one
  · exact growthPositive
  · exact chemical.fieldEquation

end
end IGSIII4
