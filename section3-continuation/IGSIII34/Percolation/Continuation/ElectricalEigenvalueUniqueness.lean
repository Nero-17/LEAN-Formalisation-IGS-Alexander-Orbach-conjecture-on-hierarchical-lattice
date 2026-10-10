import IGSIII34.Percolation.Continuation.ElectricalBoundaryMean
import IGSIII.Probability.ExponentialGrowthUniqueness
import IGSIII34.Probability.ReciprocalMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal

theorem electrical_eigenlaw_eigenvalue_eq_natural_growth (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant naturalGrowth : ℝ) (naturalGrowthPositive : 0 < naturalGrowth)
    (naturalGrowthBounds : ∀ depth, naturalGrowth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ≤ constant⁻¹*naturalGrowth^depth)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (lawIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)) (law:Measure ℝ≥0))
    (inverseIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (law:Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(law:Measure ℝ≥0)) = 1)
    (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    (growth:ℝ) = naturalGrowth := by
  have inversePositive := inverse_mean_positive (law:Measure ℝ≥0) (fun value : ℝ≥0 => (value:ℝ))
    (lawPositive.mono (fun value positive => by exact_mod_cast positive)) inverseIntegrable
  have inverseAtLeastOne : 1 ≤ ∫ value : ℝ≥0, (value:ℝ)⁻¹ ∂(law:Measure ℝ≥0) := by
    have comparison := integral_mul_reciprocal_integral_ge_one (law:Measure ℝ≥0)
      (fun value : ℝ≥0 => (value:ℝ)) NNReal.continuous_coe.measurable
      (lawPositive.mono (fun value positive => by exact_mod_cast positive)) lawIntegrable inverseIntegrable
    simpa only [meanOne, one_mul] using comparison
  have growthBounds : ∀ depth, (growth:ℝ)^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ≤
        (∫ value : ℝ≥0, (value:ℝ)⁻¹ ∂(law:Measure ℝ≥0))*(growth:ℝ)^depth := by
    intro depth
    cases depth with
    | zero => simpa only [pow_zero, electricalOrbitScale, NNReal.coe_one, mul_one] using And.intro le_rfl inverseAtLeastOne
    | succ depth =>
        have comparison := electricalBoundaryTreeIteration_mean_sandwich rule classical p positive belowOne fixedPoint law lawPositive
          lawIntegrable inverseIntegrable meanOne depth
        have meanEquality : (∫ sample, (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)
            ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) = (growth:ℝ)^(depth+1) := by
          have transport := integral_map_of_stronglyMeasurable
            (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
            (electricalBoundaryTreeIteration_measurable rule (depth+1))
            NNReal.continuous_coe.measurable.stronglyMeasurable
          rw [electricalBoundaryTreeIteration_law rule p positive belowOne fixedPoint law] at transport
          exact transport.symm.trans
            (electricalOutputLaw_iterate_eigenlaw_mean rule p positive belowOne fixedPoint law growth eigenlaw meanOne (depth+1))
        rw [meanEquality] at comparison
        exact ⟨comparison.2, ((div_le_iff₀ inversePositive).mp comparison.1).trans_eq (mul_comm _ _)⟩
  exact (exponential_growth_unique (fun depth => (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ))
    naturalGrowth (growth:ℝ) constant⁻¹ _ naturalGrowthPositive
    (by exact_mod_cast growthPositive) naturalGrowthBounds growthBounds).symm

end
end IGSIII34.Percolation
