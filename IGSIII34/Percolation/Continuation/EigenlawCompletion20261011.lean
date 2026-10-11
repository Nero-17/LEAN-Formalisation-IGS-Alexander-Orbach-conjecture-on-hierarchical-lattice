import IGSIII34.Percolation.Continuation.ElectricalEigenlawUniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace IGSIII34.Percolation
noncomputable section

open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal

/-- The paper's uniqueness class, with no auxiliary path-length hypothesis. -/
theorem electrical_positive_mean_one_eigenlaw_unique_actual_completion20261011
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (first second : ProbabilityMeasure ℝ≥0)
    (firstPositive : ∀ᵐ value ∂(first : Measure ℝ≥0), 0 < value)
    (secondPositive : ∀ᵐ value ∂(second : Measure ℝ≥0), 0 < value)
    (firstMoments : ∀ exponent : ℝ,
      Integrable (fun value : ℝ≥0 => (value : ℝ)^exponent) (first : Measure ℝ≥0))
    (secondMoments : ∀ exponent : ℝ,
      Integrable (fun value : ℝ≥0 => (value : ℝ)^exponent) (second : Measure ℝ≥0))
    (firstMeanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(first : Measure ℝ≥0)) = 1)
    (secondMeanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(second : Measure ℝ≥0)) = 1)
    (firstGrowth secondGrowth : ℝ≥0)
    (firstEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint first =
      scaledProbabilityLaw firstGrowth first)
    (secondEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint second =
      scaledProbabilityLaw secondGrowth second) :
    first = second := by
  exact electrical_positive_mean_one_eigenlaw_unique rule classical p positive belowOne fixedPoint
    (fun configuration => (network rule.network configuration).graph.dist
      rule.network.source rule.network.target)
    (fun _ _ => le_rfl) first second firstPositive secondPositive firstMoments secondMoments
    firstMeanOne secondMeanOne firstGrowth secondGrowth firstEigenlaw secondEigenlaw

/-- Once the input law is mean one, its output law determines the multiplier. -/
theorem electrical_mean_one_eigenlaw_multiplier_unique_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1)
    (firstGrowth secondGrowth : ℝ≥0)
    (firstEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law =
      scaledProbabilityLaw firstGrowth law)
    (secondEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law =
      scaledProbabilityLaw secondGrowth law) :
    firstGrowth = secondGrowth := by
  have firstMean := electricalOutputLaw_iterate_eigenlaw_mean rule p positive belowOne
    fixedPoint law firstGrowth firstEigenlaw meanOne 1
  have secondMean := electricalOutputLaw_iterate_eigenlaw_mean rule p positive belowOne
    fixedPoint law secondGrowth secondEigenlaw meanOne 1
  simp only [Function.iterate_one, pow_one] at firstMean secondMean
  exact NNReal.coe_injective (firstMean.symm.trans secondMean)

/-- The actual critical model has exactly one positive, mean-one, all-moment eigenpair.
The assertions here only collect proved actual-model results; there is no supplied
stationary field, compact cluster, existence certificate, or uniqueness premise. -/
theorem exists_unique_actual_electrical_eigenpair_completion20261011
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃! pair : ℝ≥0 × ProbabilityMeasure ℝ≥0,
      (∀ᵐ value ∂(pair.2 : Measure ℝ≥0), 0 < value) ∧
      (∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value : ℝ)^exponent)
        (pair.2 : Measure ℝ≥0)) ∧
      (∫ value : ℝ≥0, (value : ℝ) ∂(pair.2 : Measure ℝ≥0)) = 1 ∧
      electricalOutputLaw rule p positive belowOne fixedPoint pair.2 =
        scaledProbabilityLaw pair.1 pair.2 := by
  obtain ⟨law, meanOne, moments, normalizedFixed, outputMeanAboveOne, lawPositive⟩ :=
    exists_electrical_eigenlaw_all_real_moments rule classical p positive belowOne fixedPoint
  have scaling := electrical_eigenlaw_scaling rule p positive belowOne fixedPoint law
    (zero_lt_one.trans outputMeanAboveOne) normalizedFixed
  refine ⟨(Real.toNNReal (electricalOutputMean rule p positive belowOne fixedPoint law), law),
    ⟨lawPositive, moments, meanOne, scaling⟩, ?_⟩
  intro pair properties
  obtain ⟨otherPositive, otherMoments, otherMean, otherEigenlaw⟩ := properties
  have lawsEqual := electrical_positive_mean_one_eigenlaw_unique_actual_completion20261011
    rule classical p positive belowOne fixedPoint pair.2 law otherPositive lawPositive
    otherMoments moments otherMean meanOne pair.1
    (Real.toNNReal (electricalOutputMean rule p positive belowOne fixedPoint law))
    otherEigenlaw scaling
  have growthsEqual := electrical_mean_one_eigenlaw_multiplier_unique_completion20261011
    rule p positive belowOne fixedPoint law meanOne pair.1
    (Real.toNNReal (electricalOutputMean rule p positive belowOne fixedPoint law))
    (lawsEqual ▸ otherEigenlaw) scaling
  exact Prod.ext growthsEqual lawsEqual

end
end IGSIII34.Percolation
