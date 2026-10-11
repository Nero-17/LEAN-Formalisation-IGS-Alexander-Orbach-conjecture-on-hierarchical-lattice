import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion20261011
import IGSIII34.Percolation.ElectricalNormalizedUpper
import IGSIII34.Percolation.MarkedIntegral

/-! Actual conditional and mean lower bounds of the natural mean-one
electrical field. These discharge the corresponding Section 4 dependency
without assuming the finite-generation sandwich. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p)
  (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)

theorem natural_electrical_field_equation_completion20261011 :
    electricalTransfer rule natural.field =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => natural.growth * natural.field marks := by
  filter_upwards [natural.fieldStationary] with marks stationary
  have rootShiftIdentity : innovationTreeShift rule [] marks = marks := by
    funext coordinate
    rfl
  simpa only [electricalTransfer, electricalField, List.nil_append, rootShiftIdentity] using stationary []

theorem natural_electrical_conditional_lower_completion20261011 (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      natural.growth ^ (depth + 1) *
        (condExp (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
          (depth + 1)) (independentInnovationLaw rule p positive belowOne fixedPoint) (⇑natural.field)) marks ≤
      unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true) := by
  have growthPositive := zero_lt_one.trans natural.aboveOne
  have upper := normalized_electrical_boundary_conditional_mean_upper rule p positive belowOne fixedPoint
    natural.growth growthPositive.le natural.field natural.fieldPositive 1 zero_le_one natural.fieldMeanOne depth
  rw [Function.iterate_fixed natural.fieldFixed] at upper
  filter_upwards [upper] with marks bound
  have multiplied := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using bound)
    (pow_pos growthPositive (depth + 1)).le
  simpa only [inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ growthPositive.ne'), one_mul] using multiplied

theorem natural_electrical_mean_lower_completion20261011 (depth : ℕ) :
    natural.growth ^ (depth + 1) ≤
      ∫ marks, unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  have conditionalIntegrable :=
    (integrable_condExp (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
      (m := coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth + 1))
      (f := ⇑natural.field)).const_mul (natural.growth ^ (depth + 1))
  have resistanceIntegrable := marked_observable_integrable rule p positive belowOne fixedPoint depth [] true
    (unitConfigurationResistance (rule.generation depth).network)
  have bound := integral_mono_ae conditionalIntegrable resistanceIntegrable
    (natural_electrical_conditional_lower_completion20261011 rule p positive belowOne fixedPoint natural depth)
  rw [integral_const_mul, integral_condExp
    ((coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)).le (depth + 1)),
    natural.fieldMeanOne, mul_one] at bound
  exact bound

end
end IGSIII34.Percolation
