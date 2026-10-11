import IGSIII34.Percolation.Continuation.ElectricalEigenlawRealization
import IGSIII34.Percolation.Continuation.ElectricalEndogenousUniqueness
import IGSIII34.Percolation.Continuation.ElectricalEigenvalueUniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal

theorem electrical_mean_one_eigenlaw_growth_positive (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(law:Measure ℝ≥0)) = 1)
    (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    0 < growth := by
  have lawIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_one] using moments 1
  have inverseIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_neg_one] using moments (-1)
  have inversePositive := inverse_mean_positive (law:Measure ℝ≥0) (fun value : ℝ≥0 => (value:ℝ))
    (lawPositive.mono (fun value positive => by exact_mod_cast positive)) inverseIntegrable
  have comparison := (electricalBoundaryTreeIteration_mean_sandwich rule classical p positive belowOne fixedPoint
    law lawPositive lawIntegrable inverseIntegrable meanOne 0).1
  have transport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (electricalBoundaryTreeIteration_measurable rule 1) NNReal.continuous_coe.measurable.stronglyMeasurable
  rw [electricalBoundaryTreeIteration_law] at transport
  have meanEquality := transport.symm.trans
    (electricalOutputLaw_iterate_eigenlaw_mean rule p positive belowOne fixedPoint law growth eigenlaw meanOne 1)
  simp only [pow_one] at meanEquality
  rw [meanEquality] at comparison
  exact_mod_cast (div_pos (by exact_mod_cast electricalOrbitScale_positive rule classical p positive belowOne fixedPoint 1)
    inversePositive).trans_le comparison

theorem electrical_Lp_real_eigenlaw_properties (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (meanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(law:Measure ℝ≥0)) = 1)
    (inverseIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (law:Measure ℝ≥0))
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (lawEquality : (independentInnovationLaw rule p positive belowOne fixedPoint).map value =
      (law:Measure ℝ≥0).map NNReal.toReal) :
    (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
      (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
      Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      electricalFixedLaw rule p positive belowOne fixedPoint value = law := by
  have valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks := by
    have realPositive : ∀ᵐ value ∂(law:Measure ℝ≥0).map NNReal.toReal, 0 < value := by
      apply (ae_map_iff NNReal.continuous_coe.measurable.aemeasurable (measurableSet_lt measurable_const measurable_id)).mpr
      exact lawPositive.mono (fun value positive => by exact_mod_cast positive)
    rw [← lawEquality] at realPositive
    exact (ae_map_iff (Lp.stronglyMeasurable value).measurable.aemeasurable
      (measurableSet_lt measurable_const measurable_id)).mp realPositive
  have valueMeanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 := by
    have transport := integral_map_of_stronglyMeasurable
      (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
      (Lp.stronglyMeasurable value).measurable measurable_id.stronglyMeasurable
    rw [lawEquality, integral_map_of_stronglyMeasurable NNReal.continuous_coe.measurable
      measurable_id.stronglyMeasurable] at transport
    exact transport.symm.trans meanOne
  have inverseValueIntegrable : Integrable (fun marks => (value marks)⁻¹)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    have inverseRealIntegrable : Integrable (fun value : ℝ => value⁻¹) ((law:Measure ℝ≥0).map NNReal.toReal) :=
      (integrable_map_measure measurable_inv.aestronglyMeasurable NNReal.continuous_coe.measurable.aemeasurable).mpr inverseIntegrable
    rw [← lawEquality] at inverseRealIntegrable
    exact (integrable_map_measure measurable_inv.aestronglyMeasurable
      (Lp.stronglyMeasurable value).measurable.aemeasurable).mp inverseRealIntegrable
  have fixedLawEquality : electricalFixedLaw rule p positive belowOne fixedPoint value = law := by
    have transport := congrArg (fun measure : Measure ℝ => measure.map Real.toNNReal) lawEquality
    rw [Measure.map_map measurable_real_toNNReal (Lp.stronglyMeasurable value).measurable,
      Measure.map_map measurable_real_toNNReal NNReal.continuous_coe.measurable] at transport
    have identity : Real.toNNReal ∘ NNReal.toReal = id := by funext value; exact Real.toNNReal_coe
    rw [identity, Measure.map_id] at transport
    apply Subtype.ext
    change (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => Real.toNNReal (value marks)) = (law:Measure ℝ≥0)
    simpa only [Function.comp_def] using transport
  exact ⟨valuePositive, valueMeanOne, inverseValueIntegrable, fixedLawEquality⟩

theorem electrical_mean_one_eigenlaws_unique_of_fixed_cluster (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant naturalGrowth : ℝ) (constantPositive : 0 < constant) (naturalGrowthAboveOne : 1 < naturalGrowth)
    (growthBounds : ∀ depth, naturalGrowth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth:ℝ) ≤ constant⁻¹*naturalGrowth^depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 naturalGrowth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint naturalGrowth)
    (first second : ProbabilityMeasure ℝ≥0)
    (firstPositive : ∀ᵐ value ∂(first:Measure ℝ≥0), 0 < value)
    (secondPositive : ∀ᵐ value ∂(second:Measure ℝ≥0), 0 < value)
    (firstMoments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (first:Measure ℝ≥0))
    (secondMoments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (second:Measure ℝ≥0))
    (firstMeanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(first:Measure ℝ≥0)) = 1)
    (secondMeanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(second:Measure ℝ≥0)) = 1)
    (firstGrowth secondGrowth : ℝ≥0) (firstGrowthPositive : 0 < firstGrowth) (secondGrowthPositive : 0 < secondGrowth)
    (firstEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint first = scaledProbabilityLaw firstGrowth first)
    (secondEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint second = scaledProbabilityLaw secondGrowth second) :
    first = second := by
  have firstIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)) (first:Measure ℝ≥0) := by
    simpa only [Real.rpow_one] using firstMoments 1
  have secondIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)) (second:Measure ℝ≥0) := by
    simpa only [Real.rpow_one] using secondMoments 1
  have firstInverse : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (first:Measure ℝ≥0) := by
    simpa only [Real.rpow_neg_one] using firstMoments (-1)
  have secondInverse : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (second:Measure ℝ≥0) := by
    simpa only [Real.rpow_neg_one] using secondMoments (-1)
  have firstGrowthEquality := electrical_eigenlaw_eigenvalue_eq_natural_growth rule classical p positive belowOne fixedPoint
    constant naturalGrowth (zero_lt_one.trans naturalGrowthAboveOne) growthBounds first firstPositive firstIntegrable
    firstInverse firstMeanOne firstGrowth firstGrowthPositive firstEigenlaw
  have secondGrowthEquality := electrical_eigenlaw_eigenvalue_eq_natural_growth rule classical p positive belowOne fixedPoint
    constant naturalGrowth (zero_lt_one.trans naturalGrowthAboveOne) growthBounds second secondPositive secondIntegrable
    secondInverse secondMeanOne secondGrowth secondGrowthPositive secondEigenlaw
  have firstGrowthAboveOne : 1 < firstGrowth := by exact_mod_cast (firstGrowthEquality.symm ▸ naturalGrowthAboveOne)
  have secondGrowthAboveOne : 1 < secondGrowth := by exact_mod_cast (secondGrowthEquality.symm ▸ naturalGrowthAboveOne)
  obtain ⟨firstValue, firstFixed, firstLaw⟩ := electrical_eigenlaw_endogenous_fixed_Lp_exists rule p positive belowOne fixedPoint
    first firstPositive firstMoments firstGrowth firstGrowthAboveOne firstEigenlaw
  obtain ⟨secondValue, secondFixed, secondLaw⟩ := electrical_eigenlaw_endogenous_fixed_Lp_exists rule p positive belowOne fixedPoint
    second secondPositive secondMoments secondGrowth secondGrowthAboveOne secondEigenlaw
  rw [firstGrowthEquality] at firstFixed
  rw [secondGrowthEquality] at secondFixed
  obtain ⟨firstValuePositive, firstValueMean, firstValueInverse, firstFixedLaw⟩ :=
    electrical_Lp_real_eigenlaw_properties rule p positive belowOne fixedPoint first firstPositive firstMeanOne firstInverse firstValue firstLaw
  obtain ⟨secondValuePositive, secondValueMean, secondValueInverse, secondFixedLaw⟩ :=
    electrical_Lp_real_eigenlaw_properties rule p positive belowOne fixedPoint second secondPositive secondMeanOne secondInverse secondValue secondLaw
  have valuesEqual := electrical_mean_one_endogenous_fixed_unique rule classical p positive belowOne fixedPoint
    constant naturalGrowth constantPositive naturalGrowthAboveOne growthBounds endpoint endpointFixed membership
    firstValue secondValue firstFixed secondFixed firstValuePositive secondValuePositive firstValueMean secondValueMean
    firstValueInverse secondValueInverse
  rw [← firstFixedLaw, ← secondFixedLaw, valuesEqual]

theorem electrical_positive_mean_one_eigenlaw_unique (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration)
    (first second : ProbabilityMeasure ℝ≥0)
    (firstPositive : ∀ᵐ value ∂(first:Measure ℝ≥0), 0 < value)
    (secondPositive : ∀ᵐ value ∂(second:Measure ℝ≥0), 0 < value)
    (firstMoments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (first:Measure ℝ≥0))
    (secondMoments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (second:Measure ℝ≥0))
    (firstMeanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(first:Measure ℝ≥0)) = 1)
    (secondMeanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(second:Measure ℝ≥0)) = 1)
    (firstGrowth secondGrowth : ℝ≥0)
    (firstEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint first = scaledProbabilityLaw firstGrowth first)
    (secondEigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint second = scaledProbabilityLaw secondGrowth second) :
    first = second := by
  obtain ⟨constant, naturalGrowth, constantPositive, _, growthLower, _, growthBounds,
    fixed, fixedIdentity, _, _, amplitude, amplitudeLower, membership, _, _⟩ :=
    exists_actual_electrical_fixed_ray_endpoint rule classical p positive belowOne fixedPoint pathLength distanceBound
  have firstGrowthPositive := electrical_mean_one_eigenlaw_growth_positive rule classical p positive belowOne fixedPoint
    first firstPositive firstMoments firstMeanOne firstGrowth firstEigenlaw
  have secondGrowthPositive := electrical_mean_one_eigenlaw_growth_positive rule classical p positive belowOne fixedPoint
    second secondPositive secondMoments secondMeanOne secondGrowth secondEigenlaw
  have growthAboveOne := (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale).trans_le growthLower
  have endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 naturalGrowth (amplitude • fixed) = amplitude • fixed := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 naturalGrowth amplitude
      (zero_le_one.trans amplitudeLower), fixedIdentity]
  exact electrical_mean_one_eigenlaws_unique_of_fixed_cluster rule classical p positive belowOne fixedPoint
    constant naturalGrowth constantPositive growthAboveOne growthBounds (amplitude • fixed) endpointFixed membership
    first second firstPositive secondPositive firstMoments secondMoments firstMeanOne secondMeanOne
    firstGrowth secondGrowth firstGrowthPositive secondGrowthPositive firstEigenlaw secondEigenlaw

theorem electrical_positive_mean_one_output_mean_positive (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(law:Measure ℝ≥0)) = 1) :
    0 < electricalOutputMean rule p positive belowOne fixedPoint law := by
  have lawIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_one] using moments 1
  have inverseIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_neg_one] using moments (-1)
  have inversePositive := inverse_mean_positive (law:Measure ℝ≥0) (fun value : ℝ≥0 => (value:ℝ))
    (lawPositive.mono (fun value positive => by exact_mod_cast positive)) inverseIntegrable
  have comparison := (electricalBoundaryTreeIteration_mean_sandwich rule classical p positive belowOne fixedPoint
    law lawPositive lawIntegrable inverseIntegrable meanOne 0).1
  have transport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (electricalBoundaryTreeIteration_measurable rule 1) NNReal.continuous_coe.measurable.stronglyMeasurable
  rw [electricalBoundaryTreeIteration_law] at transport
  simp only [Function.iterate_one] at transport
  change electricalOutputMean rule p positive belowOne fixedPoint law = _ at transport
  rw [← transport] at comparison
  exact (div_pos (by exact_mod_cast electricalOrbitScale_positive rule classical p positive belowOne fixedPoint 1)
    inversePositive).trans_le comparison

theorem electrical_positive_mean_one_normalized_eigenlaw_unique (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration)
    (first second : ProbabilityMeasure ℝ≥0)
    (firstPositive : ∀ᵐ value ∂(first:Measure ℝ≥0), 0 < value)
    (secondPositive : ∀ᵐ value ∂(second:Measure ℝ≥0), 0 < value)
    (firstMoments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (first:Measure ℝ≥0))
    (secondMoments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (second:Measure ℝ≥0))
    (firstMeanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(first:Measure ℝ≥0)) = 1)
    (secondMeanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(second:Measure ℝ≥0)) = 1)
    (firstEigenlaw : normalizedElectricalLaw rule p positive belowOne fixedPoint first = first)
    (secondEigenlaw : normalizedElectricalLaw rule p positive belowOne fixedPoint second = second) : first = second := by
  have firstMeanPositive := electrical_positive_mean_one_output_mean_positive rule classical p positive belowOne fixedPoint
    first firstPositive firstMoments firstMeanOne
  have secondMeanPositive := electrical_positive_mean_one_output_mean_positive rule classical p positive belowOne fixedPoint
    second secondPositive secondMoments secondMeanOne
  exact electrical_positive_mean_one_eigenlaw_unique rule classical p positive belowOne fixedPoint pathLength distanceBound
    first second firstPositive secondPositive firstMoments secondMoments firstMeanOne secondMeanOne
    (Real.toNNReal (electricalOutputMean rule p positive belowOne fixedPoint first))
    (Real.toNNReal (electricalOutputMean rule p positive belowOne fixedPoint second))
    (electrical_eigenlaw_scaling rule p positive belowOne fixedPoint first firstMeanPositive firstEigenlaw)
    (electrical_eigenlaw_scaling rule p positive belowOne fixedPoint second secondMeanPositive secondEigenlaw)

end
end IGSIII34.Percolation
