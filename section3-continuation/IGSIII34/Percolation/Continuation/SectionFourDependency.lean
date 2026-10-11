import IGSIII4.AcceptedSectionThree
import IGSIII34.Percolation.Continuation.NaturalSandwichCompletion20261011

/-! The Section 4 electrical interface is inhabited by the actual natural
electrical law constructed in Section 3. No accepted electrical input remains
in this existence theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Percolation
noncomputable section
open Universality MeasureTheory IGSIII.Chemical.Substitution IGSIII.Probability

def naturalSectionFourElectrical
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    IGSIII4.AcceptedElectricalSectionThree rule p positive belowOne fixedPoint where
  growth := natural.growth
  growthAboveOne := natural.aboveOne
  field := natural.field
  fieldMeasurable := (Lp.stronglyMeasurable natural.field).measurable
  fieldIntegrable := by simpa using natural.fieldMoments 1
  fieldPositive := natural.fieldPositive
  fieldMeanOne := natural.fieldMeanOne
  fieldEquation := natural_electrical_field_equation_completion20261011
    rule p positive belowOne fixedPoint natural
  conditionalLower := by
    intro depth
    exact natural_electrical_conditional_lower_completion20261011
      rule p positive belowOne fixedPoint natural depth
  meanLower := natural_electrical_mean_lower_completion20261011
    rule p positive belowOne fixedPoint natural

theorem exists_actual_section_four_electrical
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    Nonempty (IGSIII4.AcceptedElectricalSectionThree rule p positive belowOne fixedPoint) := by
  obtain ⟨natural⟩ := exists_natural_resistance_completion20261011
    rule classicalRule p positive belowOne fixedPoint
  exact ⟨naturalSectionFourElectrical rule p positive belowOne fixedPoint natural⟩

end
end IGSIII34.Percolation
