import IGSIII34.Percolation.ElectricalBoundaryComparison
import IGSIII34.Probability.ConditionalScaledComparison
import IGSIII34.Percolation.ElectricalBoundaryIteration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem normalized_electrical_boundary_conditional_pair_comparison (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (firstPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < first marks)
    (secondPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < second marks)
    (numeratorIntegrable : Integrable (fun marks => max (positiveRepresentative first marks-positiveRepresentative second marks) 0 *
      max 1 ((positiveRepresentative second marks)⁻¹^2)) (independentInnovationLaw rule p positive belowOne fixedPoint))
    {numerator denominator : ℝ} (numeratorNonnegative : 0 ≤ numerator) (denominatorPositive : 0 < denominator)
    (numeratorEquality : (∫ marks, max (positiveRepresentative first marks-positiveRepresentative second marks) 0 *
      max 1 ((positiveRepresentative second marks)⁻¹^2) ∂independentInnovationLaw rule p positive belowOne fixedPoint) = numerator)
    (denominatorEquality : (∫ marks, min (positiveRepresentative second marks) (positiveRepresentative second marks)⁻¹
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) = denominator)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks => max
        (((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] first) marks-
          ((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] second) marks) 0 |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
      (numerator/denominator) * (independentInnovationLaw rule p positive belowOne fixedPoint)[
        ⇑((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] second) |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
  have firstRepresentative := positiveRepresentative_ae_eq _ firstPositive
  have secondRepresentative := positiveRepresentative_ae_eq _ secondPositive
  have comparison := actual_electrical_boundary_conditional_pair_comparison rule p positive belowOne fixedPoint
    (positiveRepresentative first) (positiveRepresentative second)
    (positiveRepresentative_measurable (Lp.stronglyMeasurable first).measurable)
    (positiveRepresentative_measurable (Lp.stronglyMeasurable second).measurable)
    (positiveRepresentative_positive first) (positiveRepresentative_positive second)
    (((Lp.memLp first).integrable (by norm_num)).congr firstRepresentative.symm)
    (((Lp.memLp second).integrable (by norm_num)).congr secondRepresentative.symm)
    numeratorIntegrable numeratorNonnegative denominatorPositive numeratorEquality denominatorEquality depth
  exact condExp_scaled_positive_part_comparison
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
    _ _ _ _ ((growth⁻¹)^(depth+1)) (numerator/denominator)
    (pow_nonneg (inv_nonneg.mpr growthNonnegative) _)
    (normalizedElectricalTransferLp_iterate_weighted_actual_ae rule p positive belowOne fixedPoint growth growthNonnegative first firstPositive depth)
    (normalizedElectricalTransferLp_iterate_weighted_actual_ae rule p positive belowOne fixedPoint growth growthNonnegative second secondPositive depth)
    comparison

end
end IGSIII34.Percolation

