import IGSIII34.Percolation.ElectricalBoundaryUpper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem normalized_electrical_boundary_conditional_mean_upper (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (mean : ℝ) (meanNonnegative : 0 ≤ mean)
    (meanEquality : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = mean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[
        ⇑((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] value) |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
      mean * ((growth⁻¹)^(depth+1)*unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true)) := by
  have weighted := normalizedElectricalTransferLp_iterate_weighted_actual_ae rule p positive belowOne fixedPoint
    growth growthNonnegative value valuePositive depth
  have conditionalEquality := condExp_congr_ae (m := coordinatePrefixFiltration
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)) weighted
  have scalarEquality := condExp_smul (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
    ((growth⁻¹)^(depth+1))
    (fun marks => electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
      (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)))
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
  have upper := actual_electrical_boundary_conditional_mean_upper rule p positive belowOne fixedPoint value valuePositive
    mean meanNonnegative meanEquality depth
  filter_upwards [conditionalEquality, scalarEquality, upper] with marks conditional scalar inequality
  rw [conditional]
  change (independentInnovationLaw rule p positive belowOne fixedPoint)[((growth⁻¹)^(depth+1)) •
    (fun marks => electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
      (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))) |
      coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤ _
  rw [scalar, Pi.smul_apply, smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left inequality (pow_nonneg (inv_nonneg.mpr growthNonnegative) _)).trans_eq (by ring)

end
end IGSIII34.Percolation

