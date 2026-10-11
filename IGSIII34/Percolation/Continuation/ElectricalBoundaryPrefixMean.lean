import IGSIII34.Percolation.Continuation.ElectricalBoundaryLawApproximation
import IGSIII34.Probability.IndependentConditioning

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal

private def electricalBoundaryMeanPrefixIndex (rule : Rule) (depth : ℕ) : Bool → Type
  | false => {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1}
  | true => Fin (rule.generation depth).edges

private def electricalBoundaryMeanPrefixCoordinate (rule : Rule) (depth : ℕ) :
    ((group : Bool) × electricalBoundaryMeanPrefixIndex rule depth group) → List (Fin rule.edges) × Bool
  | ⟨false, coordinate⟩ => coordinate.val
  | ⟨true, leaf⟩ => (generationEdgeAddress rule depth leaf, true)

private theorem electricalBoundaryMeanPrefixCoordinate_injective (rule : Rule) (depth : ℕ) :
    Function.Injective (electricalBoundaryMeanPrefixCoordinate rule depth) := by
  rintro ⟨firstGroup, first⟩ ⟨secondGroup, second⟩ equality
  cases firstGroup <;> cases secondGroup
  · have same : first.val = second.val := equality
    cases Subtype.ext same
    rfl
  · change first.val = (generationEdgeAddress rule depth second, true) at equality
    have lengths := congrArg (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) equality
    rw [generationEdgeAddress_length] at lengths
    have short := first.property
    omega
  · change (generationEdgeAddress rule depth first, true) = second.val at equality
    have lengths := congrArg (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) equality
    rw [generationEdgeAddress_length] at lengths
    have short := second.property
    omega
  · have same := generationEdgeAddress_injective rule depth (congrArg Prod.fst equality)
    cases same
    rfl

theorem electricalBoundaryTree_marks_prefix_frontier_independent (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) :
    IndepFun
      (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
        fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} =>
          (sample coordinate.val).1)
      (fun sample leaf => (sample (generationEdgeAddress rule depth leaf, true)).2)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have independent := infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law:Measure ℝ≥0))
    (electricalBoundaryMeanPrefixCoordinate rule depth) (electricalBoundaryMeanPrefixCoordinate_injective rule depth)
  have two := independent.indepFun (i := false) (j := true) Bool.false_ne_true
  exact two.comp
    (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))
    (measurable_pi_lambda _ (fun leaf => measurable_snd.comp (measurable_pi_apply leaf)))

theorem electricalBoundaryTreeIteration_condExp_marks_prefix (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (depth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)[
      fun sample => (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ) |
        (inferInstance : MeasurableSpace
          ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} → Configuration rule.edges)).comap
          (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
            fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} =>
              (sample coordinate.val).1)] =ᵐ[
        electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
        fun sample => electricalBoundaryGenerationMean rule law depth (fun coordinate => (sample coordinate).1) := by
  let response (data :
      ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} → Configuration rule.edges) ×
        (Fin (rule.generation depth).edges → ℝ≥0)) : ℝ :=
    electricalCell (rule.generation depth).network
      (markedGenerationConfiguration rule (innovationPrefixFill rule (depth+1) data.1) depth [] true)
      (fun edge => (data.2 edge:ℝ))
  have responseMeasurable : Measurable response :=
    (NNReal.continuous_coe.comp (electricalCellNNReal_joint_continuous
      (rule.generation depth).network)).measurable.comp
      (((markedGenerationConfiguration_measurable rule depth [] true).comp
        ((innovationPrefixFill_measurable rule (depth+1)).comp measurable_fst)).prodMk measurable_snd)
  have responseEquality : (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      response ((fun coordinate => (sample coordinate.val).1),
        fun leaf => (sample (generationEdgeAddress rule depth leaf, true)).2)) =ᵐ[
        electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
        fun sample => (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ) := by
    have weighted := electricalBoundaryTreeIteration_weighted_coe_ae rule p positive belowOne fixedPoint
      law lawPositive depth
    filter_upwards [weighted] with sample weighted
    dsimp only [response]
    rw [markedGenerationConfiguration_prefix_factor rule (fun coordinate => (sample coordinate).1) depth true]
    exact weighted.symm
  have configurationLawProbability : IsProbabilityMeasure
      ((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true)) :=
    Measure.isProbabilityMeasure_map (markedGenerationConfiguration_measurable rule depth [] true).aemeasurable
  letI := configurationLawProbability
  have jointMeasurable : Measurable (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true,
        fun leaf : Fin (rule.generation depth).edges => (sample (generationEdgeAddress rule depth leaf, true)).2)) :=
    ((markedGenerationConfiguration_measurable rule depth [] true).comp
      (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))).prodMk
      (measurable_pi_lambda _ (fun leaf => measurable_snd.comp
        (measurable_pi_apply (generationEdgeAddress rule depth leaf, true))))
  have jointPreserving : MeasurePreserving _ (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true)).prod
          (Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))) :=
    ⟨jointMeasurable, electricalBoundaryTree_configuration_frontier_map rule p positive belowOne fixedPoint law depth⟩
  have squareIntegrable := jointPreserving.integrable_comp_of_integrable
    (electricalCell_nnreal_product_square_integrable (rule.generation depth).network _ law secondMoment)
  have squareMeasurable : AEStronglyMeasurable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true)
        (fun leaf => ((sample (generationEdgeAddress rule depth leaf, true)).2:ℝ)))
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) :=
    ((NNReal.continuous_coe.comp (electricalCellNNReal_joint_continuous
      (rule.generation depth).network)).measurable.comp jointMeasurable).aestronglyMeasurable
  have weightedIntegrable := ((memLp_two_iff_integrable_sq squareMeasurable).mpr squareIntegrable).integrable
    (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have responseIntegrable : Integrable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      response ((fun coordinate => (sample coordinate.val).1),
        fun leaf => (sample (generationEdgeAddress rule depth leaf, true)).2))
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
    apply weightedIntegrable.congr
    filter_upwards [] with sample
    dsimp only [response]
    rw [markedGenerationConfiguration_prefix_factor rule (fun coordinate => (sample coordinate).1) depth true]
  have conditional := independent_pair_condExp_eq_integral
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} =>
        (sample coordinate.val).1)
    (fun sample leaf => (sample (generationEdgeAddress rule depth leaf, true)).2)
    (by fun_prop) (by fun_prop)
    (electricalBoundaryTree_marks_prefix_frontier_independent rule p positive belowOne fixedPoint law depth)
    response responseMeasurable.stronglyMeasurable responseIntegrable
  rw [electricalBoundaryTree_frontier_map] at conditional
  refine (condExp_congr_ae responseEquality).symm.trans ?_
  filter_upwards [conditional] with sample conditional
  dsimp only [response] at conditional
  rw [markedGenerationConfiguration_prefix_factor rule (fun coordinate => (sample coordinate).1) depth true] at conditional
  exact conditional

theorem electricalBoundaryGenerationMean_eigenlaw_mean (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(law:Measure ℝ≥0)) = 1)
    (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    (∫ marks, electricalBoundaryGenerationMean rule law depth marks
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) = (growth:ℝ)^(depth+1) := by
  have prefixMeasurable : Measurable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} =>
        (sample coordinate.val).1) := by fun_prop
  have conditionalIntegral := integral_congr_ae
    (electricalBoundaryTreeIteration_condExp_marks_prefix rule p positive belowOne fixedPoint
      law lawPositive secondMoment depth)
  rw [integral_condExp prefixMeasurable.comap_le] at conditionalIntegral
  have meanTransport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (show Measurable (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate => (sample coordinate).1) from by fun_prop)
    (electricalBoundaryGenerationMean_measurable rule law depth).stronglyMeasurable
  rw [electricalBoundaryInnovationLaw_marks_map] at meanTransport
  rw [meanTransport, ← conditionalIntegral]
  have treeTransport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (electricalBoundaryTreeIteration_measurable rule (depth+1)) NNReal.continuous_coe.measurable.stronglyMeasurable
  rw [electricalBoundaryTreeIteration_law] at treeTransport
  exact treeTransport.symm.trans
    (electricalOutputLaw_iterate_eigenlaw_mean rule p positive belowOne fixedPoint law growth eigenlaw meanOne (depth+1))

end
end IGSIII34.Percolation
