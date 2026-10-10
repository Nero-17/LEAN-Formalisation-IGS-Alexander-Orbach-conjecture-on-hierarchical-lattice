import IGSIII34.Percolation.Continuation.ElectricalEigenvalueUniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal

theorem electrical_normalized_eigenlaw_output_mean_eq_natural_growth (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant naturalGrowth : ℝ) (naturalGrowthPositive : 0 < naturalGrowth)
    (naturalGrowthBounds : ∀ depth, naturalGrowth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ≤ constant⁻¹*naturalGrowth^depth)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(law:Measure ℝ≥0)) = 1)
    (eigenlaw : normalizedElectricalLaw rule p positive belowOne fixedPoint law = law) :
    electricalOutputMean rule p positive belowOne fixedPoint law = naturalGrowth := by
  have lawIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_one] using moments 1
  have inverseIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_neg_one] using moments (-1)
  have inversePositive := inverse_mean_positive (law:Measure ℝ≥0) (fun value : ℝ≥0 => (value:ℝ))
    (lawPositive.mono (fun value positive => by exact_mod_cast positive)) inverseIntegrable
  have comparison := (electricalBoundaryTreeIteration_mean_sandwich rule classical p positive belowOne fixedPoint law lawPositive
    lawIntegrable inverseIntegrable meanOne 0).1
  have transport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (electricalBoundaryTreeIteration_measurable rule 1) NNReal.continuous_coe.measurable.stronglyMeasurable
  rw [electricalBoundaryTreeIteration_law rule p positive belowOne fixedPoint law] at transport
  simp only [Function.iterate_one] at transport
  change electricalOutputMean rule p positive belowOne fixedPoint law = _ at transport
  rw [← transport] at comparison
  have meanPositive : 0 < electricalOutputMean rule p positive belowOne fixedPoint law :=
    (div_pos (by exact_mod_cast electricalOrbitScale_positive rule classical p positive belowOne fixedPoint 1)
      inversePositive).trans_le comparison
  have scaling := electrical_eigenlaw_scaling rule p positive belowOne fixedPoint law meanPositive eigenlaw
  have equality := electrical_eigenlaw_eigenvalue_eq_natural_growth rule classical p positive belowOne fixedPoint
    constant naturalGrowth naturalGrowthPositive naturalGrowthBounds law lawPositive lawIntegrable inverseIntegrable meanOne
    (Real.toNNReal (electricalOutputMean rule p positive belowOne fixedPoint law)) (Real.toNNReal_pos.mpr meanPositive) scaling
  simpa only [Real.coe_toNNReal _ meanPositive.le] using equality

end
end IGSIII34.Percolation
