import IGSIII34.Percolation.Continuation.ElectricalBoundaryVarianceDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Chemical.Substitution
open scoped NNReal ENNReal BigOperators _root_.Topology

def electricalBoundaryGenerationMean (rule : Rule) (law : ProbabilityMeasure ℝ≥0)
    (depth : ℕ) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
    electricalCell (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true) (fun edge => (input edge:ℝ))
      ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))

theorem electricalBoundaryGenerationMean_measurable (rule : Rule) (law : ProbabilityMeasure ℝ≥0)
    (depth : ℕ) : Measurable (electricalBoundaryGenerationMean rule law depth) :=
  (measurable_of_countable (fun configuration : Configuration (rule.generation depth).edges =>
    ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
      electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
      ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))).comp
    (markedGenerationConfiguration_measurable rule depth [] true)

theorem electricalBoundaryTreeIteration_normalized_eigenlaw (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample => (growth^depth)⁻¹*electricalBoundaryTreeIteration rule depth sample) =
      (law:Measure ℝ≥0) := by
  change (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
    ((fun value : ℝ≥0 => (growth^depth)⁻¹*value) ∘ electricalBoundaryTreeIteration rule depth) = _
  rw [← Measure.map_map (g := fun value : ℝ≥0 => (growth^depth)⁻¹*value)
    (measurable_const.mul measurable_id) (electricalBoundaryTreeIteration_measurable rule depth),
    electricalBoundaryTreeIteration_law,
    electricalOutputLaw_iterate_eigenlaw rule p positive belowOne fixedPoint law growth eigenlaw depth]
  rw [← scaledProbabilityLaw_measure, scaledProbabilityLaw_comp,
    inv_mul_cancel₀ (pow_ne_zero _ growthPositive.ne'), scaledProbabilityLaw_one]

theorem electricalBoundaryTreeIteration_centered_square_integral (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (depth : ℕ) :
    (∫ sample, ((electricalBoundaryTreeIteration rule (depth+1) sample:ℝ) -
      electricalBoundaryGenerationMean rule law depth (fun coordinate => (sample coordinate).1))^2
        ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) =
      electricalBoundaryGenerationVariance rule p positive belowOne fixedPoint law depth := by
  let configurationLaw := (independentInnovationLaw rule p positive belowOne fixedPoint).map
    (fun marks => markedGenerationConfiguration rule marks depth [] true)
  letI : IsProbabilityMeasure configurationLaw := Measure.isProbabilityMeasure_map
    (markedGenerationConfiguration_measurable rule depth [] true).aemeasurable
  have centeredMeasurable : Measurable (fun data :
      Configuration (rule.generation depth).edges × (Fin (rule.generation depth).edges → ℝ≥0) =>
      (electricalCell (rule.generation depth).network data.1 (fun edge => (data.2 edge:ℝ)) -
        ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
          electricalCell (rule.generation depth).network data.1 (fun edge => (input edge:ℝ))
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))^2) := by
    have meanMeasurable : Measurable (fun configuration : Configuration (rule.generation depth).edges =>
        ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
          electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))) :=
      measurable_of_countable _
    exact ((NNReal.continuous_coe.comp (electricalCellNNReal_joint_continuous
      (rule.generation depth).network)).measurable.sub (meanMeasurable.comp measurable_fst)).pow_const 2
  have centeredIntegrable : Integrable (fun data :
      Configuration (rule.generation depth).edges × (Fin (rule.generation depth).edges → ℝ≥0) =>
      (electricalCell (rule.generation depth).network data.1 (fun edge => (data.2 edge:ℝ)) -
        ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
          electricalCell (rule.generation depth).network data.1 (fun edge => (input edge:ℝ))
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))^2)
      (configurationLaw.prod (Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))) := by
    apply (integrable_prod_iff centeredMeasurable.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall ?_, Integrable.of_finite⟩
    intro configuration
    have responseMeasurable : Measurable (fun input : Fin (rule.generation depth).edges → ℝ≥0 =>
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))) :=
      (NNReal.continuous_coe.comp (electricalCellNNReal_continuous
        (rule.generation depth).network configuration)).measurable
    have responseMemLp := (memLp_two_iff_integrable_sq responseMeasurable.aestronglyMeasurable).mpr
      (electricalCell_nnreal_square_integrable (rule.generation depth).network configuration law secondMoment)
    simpa only [Pi.sub_apply, Prod.fst, Prod.snd] using (memLp_two_iff_integrable_sq
      (responseMeasurable.sub measurable_const).aestronglyMeasurable).mp
      (responseMemLp.sub (memLp_const (∫ input : Fin (rule.generation depth).edges → ℝ≥0,
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
        ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))))
  have jointMeasurable : Measurable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true,
        fun leaf : Fin (rule.generation depth).edges =>
          (sample (generationEdgeAddress rule depth leaf, true)).2)) :=
    ((markedGenerationConfiguration_measurable rule depth [] true).comp
      (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))).prodMk
      (measurable_pi_lambda _ (fun leaf => measurable_snd.comp
        (measurable_pi_apply (generationEdgeAddress rule depth leaf, true))))
  have transport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    jointMeasurable centeredMeasurable.stronglyMeasurable
  rw [electricalBoundaryTree_configuration_frontier_map] at transport
  have responseEquality := electricalBoundaryTreeIteration_weighted_coe_ae
    rule p positive belowOne fixedPoint law lawPositive depth
  have centeredEquality : (fun sample => ((electricalBoundaryTreeIteration rule (depth+1) sample:ℝ) -
      electricalBoundaryGenerationMean rule law depth (fun coordinate => (sample coordinate).1))^2) =ᵐ[
      electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
      fun sample => (electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true)
        (fun leaf => ((sample (generationEdgeAddress rule depth leaf, true)).2:ℝ)) -
          electricalBoundaryGenerationMean rule law depth (fun coordinate => (sample coordinate).1))^2 := by
    filter_upwards [responseEquality] with sample equality
    change (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ) =
      electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true)
        (fun leaf => ((sample (generationEdgeAddress rule depth leaf, true)).2:ℝ)) at equality
    rw [equality]
  rw [integral_congr_ae centeredEquality]
  unfold electricalBoundaryGenerationMean
  rw [← transport]
  exact integral_prod _ centeredIntegrable

theorem electricalBoundaryTreeIteration_normalized_centered_square_integral (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (depth : ℕ) :
    (∫ sample, ((electricalBoundaryTreeIteration rule (depth+1) sample:ℝ) / (growth:ℝ)^(depth+1) -
      electricalBoundaryGenerationMean rule law depth (fun coordinate => (sample coordinate).1) /
        (growth:ℝ)^(depth+1))^2
        ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) =
      electricalBoundaryGenerationVariance rule p positive belowOne fixedPoint law depth /
        (growth:ℝ)^(2*(depth+1)) := by
  simp_rw [← sub_div, div_pow]
  rw [integral_div, electricalBoundaryTreeIteration_centered_square_integral
    rule p positive belowOne fixedPoint law lawPositive secondMoment depth]
  congr 1
  rw [← pow_mul, Nat.mul_comm]

theorem electricalBoundaryTreeIteration_normalized_centered_square_tendsto_zero (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthAboveOne : 1 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    Tendsto (fun depth => ∫ sample,
      ((electricalBoundaryTreeIteration rule (depth+1) sample:ℝ) / (growth:ℝ)^(depth+1) -
        electricalBoundaryGenerationMean rule law depth (fun coordinate => (sample coordinate).1) /
          (growth:ℝ)^(depth+1))^2
        ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) atTop (𝓝 0) := by
  have secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_two] using moments 2
  simp_rw [electricalBoundaryTreeIteration_normalized_centered_square_integral
    rule p positive belowOne fixedPoint law lawPositive secondMoment growth]
  exact electrical_eigenlaw_generation_boundary_variance_tendsto_zero rule p positive belowOne fixedPoint
    law lawPositive moments growth growthAboveOne eigenlaw

theorem electricalBoundaryGenerationMean_second_moment_bound (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    (∫ marks, (electricalBoundaryGenerationMean rule law depth marks)^2
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
        (growth:ℝ)^(2*(depth+1))*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) := by
  have pointwise (configuration : Configuration (rule.generation depth).edges) :
      (∫ input : Fin (rule.generation depth).edges → ℝ≥0,
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))^2 ≤
        ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
          electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))^2
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)) := by
    have measurable : Measurable (fun input : Fin (rule.generation depth).edges → ℝ≥0 =>
      electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))) :=
      (NNReal.continuous_coe.comp (electricalCellNNReal_continuous
        (rule.generation depth).network configuration)).measurable
    have memLp := (memLp_two_iff_integrable_sq measurable.aestronglyMeasurable).mpr
      (electricalCell_nnreal_square_integrable (rule.generation depth).network configuration law secondMoment)
    have nonnegative := variance_nonneg (fun input : Fin (rule.generation depth).edges → ℝ≥0 =>
      electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ)))
      (Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))
    rw [variance_eq_sub memLp] at nonnegative
    simp only [Pi.pow_apply] at nonnegative
    linarith
  rw [← electricalBoundaryTree_eigenlaw_generation_second_moment rule p positive belowOne fixedPoint
    law lawPositive secondMoment growth eigenlaw depth]
  rw [integral_map_of_stronglyMeasurable (markedGenerationConfiguration_measurable rule depth [] true)
    (measurable_of_countable _).stronglyMeasurable]
  have meanSquareIntegrable : Integrable (fun marks => (electricalBoundaryGenerationMean rule law depth marks)^2)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    exact ((Integrable.of_finite : Integrable (fun configuration : Configuration (rule.generation depth).edges =>
      (∫ input : Fin (rule.generation depth).edges → ℝ≥0,
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))^2)
      ((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true))).comp_measurable
      (markedGenerationConfiguration_measurable rule depth [] true))
  have secondSquareIntegrable : Integrable (fun marks =>
      ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
        electricalCell (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true) (fun edge => (input edge:ℝ))^2
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    exact ((Integrable.of_finite : Integrable (fun configuration : Configuration (rule.generation depth).edges =>
      ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))^2
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))
      ((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true))).comp_measurable
      (markedGenerationConfiguration_measurable rule depth [] true))
  exact integral_mono meanSquareIntegrable secondSquareIntegrable
    (fun marks => pointwise (markedGenerationConfiguration rule marks depth [] true))

end
end IGSIII34.Percolation
