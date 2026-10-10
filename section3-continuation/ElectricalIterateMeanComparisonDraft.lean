import IGSIII34.Percolation.ElectricalNormalizedComparison
import IGSIII34.Probability.ElectricalComparisonWeight
import IGSIII34.Probability.ElectricalDenominator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory

def electricalComparisonCoefficient
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (first second : Sample → ℝ) : ℝ :=
  (∫ sample, max (first sample-second sample) 0 * max 1 ((second sample)⁻¹^2) ∂measure) /
    (∫ sample, min (second sample) (second sample)⁻¹ ∂measure)

theorem integral_positive_part_le_of_condExp
    {Sample : Type*} [ambient : MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (information : MeasurableSpace Sample) (informationLe : information ≤ ambient)
    (first second : Sample → ℝ) (coefficient : ℝ)
    (comparison : ∀ᵐ sample ∂measure,
      measure[fun sample => max (first sample-second sample) 0 | information] sample ≤
        coefficient * measure[second | information] sample) :
    (∫ sample, max (first sample-second sample) 0 ∂measure) ≤ coefficient * ∫ sample, second sample ∂measure := by
  have integrated := integral_mono_ae (integrable_condExp (μ := measure) (m := information)
    (f := fun sample => max (first sample-second sample) 0))
    ((integrable_condExp (μ := measure) (m := information) (f := second)).const_mul coefficient) comparison
  rw [integral_condExp informationLe, integral_const_mul, integral_condExp informationLe] at integrated
  exact integrated

end
end IGSIII34.Probability
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem normalized_electrical_iterate_positive_part_mean_le (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (firstPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < first marks)
    (secondPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < second marks)
    (inverseFourth : Integrable (fun marks => (second marks)⁻¹^4) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (depth : ℕ) :
    (∫ marks, max
      (((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] first) marks-
        ((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] second) marks) 0
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
    electricalComparisonCoefficient (independentInnovationLaw rule p positive belowOne fixedPoint) first second *
      ∫ marks, ((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] second) marks
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  have firstEquality := positiveRepresentative_ae_eq _ firstPositive
  have secondEquality := positiveRepresentative_ae_eq _ secondPositive
  have numeratorEquality : (fun marks => max (positiveRepresentative first marks-positiveRepresentative second marks) 0 *
      max 1 ((positiveRepresentative second marks)⁻¹^2)) =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      (fun marks => max (first marks-second marks) 0 * max 1 ((second marks)⁻¹^2)) := by
    filter_upwards [firstEquality, secondEquality] with marks firstEquality secondEquality
    rw [firstEquality, secondEquality]
  have denominatorEquality : (fun marks => min (positiveRepresentative second marks) (positiveRepresentative second marks)⁻¹) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] (fun marks => min (second marks) (second marks)⁻¹) := by
    filter_upwards [secondEquality] with marks equality
    rw [equality]
  have numeratorIntegrable := (electricalComparison_numerator_integrable
    (independentInnovationLaw rule p positive belowOne fixedPoint) first second inverseFourth).congr numeratorEquality.symm
  have denominatorPositive : 0 < ∫ marks, min (positiveRepresentative second marks) (positiveRepresentative second marks)⁻¹
      ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
    rw [integral_congr_ae denominatorEquality]
    exact electrical_comparison_denominator_mean_positive _ second secondPositive
  have conditional := normalized_electrical_boundary_conditional_pair_comparison rule p positive belowOne fixedPoint
    growth growthNonnegative first second firstPositive secondPositive numeratorIntegrable
    (integral_nonneg (fun marks => mul_nonneg (le_max_right _ _) (zero_le_one.trans (le_max_left _ _))))
    denominatorPositive rfl rfl depth
  have integrated := integral_positive_part_le_of_condExp
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
    ((coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)).le (depth+1))
    _ _ _ conditional
  rw [integral_congr_ae numeratorEquality, integral_congr_ae denominatorEquality] at integrated
  exact integrated

end
end IGSIII34.Percolation


