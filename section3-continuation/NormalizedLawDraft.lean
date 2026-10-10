import IGSIII34.Percolation.OutputMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open _root_.Topology
open scoped NNReal ENNReal

def electricalOutputMean (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) : ℝ :=
  ∫ value : ℝ≥0, (value : ℝ)
    ∂(electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)

def normalizedElectricalLaw (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) : ProbabilityMeasure ℝ≥0 :=
  scaledProbabilityLaw (Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹)
    (electricalOutputLaw rule parameter positive belowOne fixedPoint law)

theorem normalizedElectricalLaw_mean (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanPositive : 0 < electricalOutputMean rule parameter positive belowOne fixedPoint law) :
    (∫ value : ℝ≥0, (value : ℝ)
      ∂(normalizedElectricalLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)) = 1 := by
  unfold normalizedElectricalLaw
  rw [scaledProbabilityLaw_mean, Real.coe_toNNReal _ (inv_nonneg.mpr meanPositive.le)]
  exact inv_mul_cancel₀ meanPositive.ne'

theorem electricalOutputMean_continuous_on_secondMoment_sublevel
    (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (bound : ℝ≥0) :
    Continuous (fun law : {law : ProbabilityMeasure ℝ≥0 |
        (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound} =>
      electricalOutputMean rule parameter positive belowOne fixedPoint law.val) := by
  let output : {law : ProbabilityMeasure ℝ≥0 |
      (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound} →
      {law : ProbabilityMeasure ℝ≥0 |
        (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ (rule.edges : ℝ≥0) ^ 2 * bound} :=
    fun law => ⟨electricalOutputLaw rule parameter positive belowOne fixedPoint law.val,
      electricalOutputLaw_secondMoment_bound rule parameter positive belowOne fixedPoint law.val bound law.property⟩
  have outputContinuous : Continuous output :=
    ((electricalOutputLaw_continuous rule parameter positive belowOne fixedPoint).comp
      continuous_subtype_val).subtype_mk _
  exact (IGSIII34.Probability.continuous_firstMoment_on_secondMoment_sublevel
    ((rule.edges : ℝ≥0) ^ 2 * bound)).comp outputContinuous

theorem normalizedElectricalLaw_continuous_on_family
    (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (bound : ℝ≥0)
    (family : Set (ProbabilityMeasure ℝ≥0))
    (momentBound : ∀ law ∈ family,
      (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound)
    (meanPositive : ∀ law ∈ family,
      0 < electricalOutputMean rule parameter positive belowOne fixedPoint law) :
    Continuous (fun law : family =>
      normalizedElectricalLaw rule parameter positive belowOne fixedPoint law.val) := by
  unfold normalizedElectricalLaw
  let inclusion : family →
      {law : ProbabilityMeasure ℝ≥0 |
        (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound} :=
    fun law => ⟨law.val, momentBound law.val law.property⟩
  have inclusionContinuous : Continuous inclusion := continuous_subtype_val.subtype_mk _
  have meanContinuous : Continuous (fun law : family =>
      electricalOutputMean rule parameter positive belowOne fixedPoint law.val) :=
    (electricalOutputMean_continuous_on_secondMoment_sublevel
    rule parameter positive belowOne fixedPoint bound).comp inclusionContinuous
  have inverseContinuous : Continuous (fun law : family =>
      (electricalOutputMean rule parameter positive belowOne fixedPoint law.val)⁻¹) :=
    meanContinuous.inv₀ (fun law => (meanPositive law.val law.property).ne')
  have scalarContinuous : Continuous (fun law : family =>
      Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law.val)⁻¹) :=
    continuous_real_toNNReal.comp inverseContinuous
  have outputContinuous : Continuous (fun law : family =>
      electricalOutputLaw rule parameter positive belowOne fixedPoint law.val) :=
    (electricalOutputLaw_continuous rule parameter positive belowOne fixedPoint).comp continuous_subtype_val
  have result : Continuous ((fun data : ℝ≥0 × ProbabilityMeasure ℝ≥0 =>
      scaledProbabilityLaw data.1 data.2) ∘
      (fun law : family => (Real.toNNReal ((electricalOutputMean rule parameter positive belowOne fixedPoint law.val)⁻¹),
        electricalOutputLaw rule parameter positive belowOne fixedPoint law.val))) :=
    scaledProbabilityLaw_continuous.comp (scalarContinuous.prodMk outputContinuous)
  simpa only [Function.comp_def] using result

end
end IGSIII34.Percolation
