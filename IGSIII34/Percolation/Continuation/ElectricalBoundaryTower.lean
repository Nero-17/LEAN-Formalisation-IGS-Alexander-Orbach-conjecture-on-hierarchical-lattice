import IGSIII34.Percolation.Continuation.ElectricalBoundaryTreeFrontier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal

theorem electricalBoundaryGenerationMean_scaled (rule : Rule) (law : ProbabilityMeasure ℝ≥0)
    (scalar : ℝ≥0) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    electricalBoundaryGenerationMean rule (scaledProbabilityLaw scalar law) depth marks =
      (scalar:ℝ)*electricalBoundaryGenerationMean rule law depth marks := by
  have inputLaw : (Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))).map
      (fun input edge => scalar*input edge) =
      Measure.pi (fun _ : Fin (rule.generation depth).edges => (scaledProbabilityLaw scalar law:Measure ℝ≥0)) := by
    simp only [scaledProbabilityLaw_measure]
    exact Measure.pi_map_pi (fun _ => (measurable_const.mul measurable_id).aemeasurable)
  unfold electricalBoundaryGenerationMean
  rw [← inputLaw, integral_map_of_stronglyMeasurable
    (φ := fun input : Fin (rule.generation depth).edges → ℝ≥0 => fun edge => scalar*input edge)
    (f := fun input : Fin (rule.generation depth).edges → ℝ≥0 =>
      electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
        (fun edge => (input edge:ℝ))) (by fun_prop)
    (NNReal.continuous_coe.comp (electricalCellNNReal_continuous
      (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))).measurable.stronglyMeasurable]
  have responseEquality (input : Fin (rule.generation depth).edges → ℝ≥0) :
      electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
        (fun edge => (scalar*input edge:ℝ≥0)) =
      (scalar:ℝ)*electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
        (fun edge => (input edge:ℝ)) :=
    congrArg NNReal.toReal (electricalCellNNReal_scale (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true) input scalar)
  simp_rw [responseEquality]
  exact integral_const_mul _ _

theorem electricalBoundaryTreeIteration_positive_actual (rule : Rule)
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0)
    (crossing : ∀ address, rule.network.crosses (sample (address, true)).1 = true)
    (positive : ∀ address, 0 < (sample (address, true)).2) (depth : ℕ) (address : List (Fin rule.edges)) :
    0 < electricalBoundaryTreeIteration rule depth (electricalBoundaryTreeShift rule address sample) := by
  induction depth generalizing address with
  | zero => simpa only [electricalBoundaryTreeIteration, electricalBoundaryTreeShift, List.append_nil] using positive address
  | succ depth previous =>
      change 0 < (electricalCell rule.network (sample (address++[], true)).1
        (fun edge => (electricalBoundaryTreeIteration rule depth
          (electricalBoundaryTreeShift rule [edge] (electricalBoundaryTreeShift rule address sample)):ℝ)))
      simp only [List.append_nil, electricalBoundaryTreeShift_append]
      exact (network rule.network (sample (address, true)).1).effectiveResistance_pos_of_connected
        (connected_of_crosses _ _ (crossing address))
        (fun edge => by exact_mod_cast previous (address++[edge.val]))

theorem electricalBoundaryTreeIteration_add_weighted_ae (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (outerDepth innerDepth : ℕ) :
    (fun sample => (electricalBoundaryTreeIteration rule ((outerDepth+1)+innerDepth) sample:ℝ)) =ᵐ[
      electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
      fun sample => electricalCell (rule.generation outerDepth).network
        (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) outerDepth [] true)
        (fun leaf => (electricalBoundaryTreeIteration rule innerDepth
          (electricalBoundaryTreeShift rule (generationEdgeAddress rule outerDepth leaf) sample):ℝ)) := by
  have marksPreserving : MeasurePreserving (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => fun coordinate => (sample coordinate).1)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    ⟨by fun_prop, electricalBoundaryInnovationLaw_marks_map rule p positive belowOne fixedPoint law⟩
  have crossing := marksPreserving.quasiMeasurePreserving.ae
    (independentInnovationLaw_crosses rule p positive belowOne fixedPoint)
  have boundaryPositive := ae_all_iff.mpr (fun address : List (Fin rule.edges) =>
    (electricalBoundaryInnovationLaw_boundary_preserving rule p positive belowOne fixedPoint law address).quasiMeasurePreserving.ae lawPositive)
  filter_upwards [crossing, boundaryPositive] with sample crossing boundaryPositive
  rw [electricalBoundaryTreeIteration_add]
  have weighted := electricalBoundaryTreeIteration_weighted_actual rule
    (electricalBoundaryTreeGraft rule innerDepth sample) crossing
    (fun address => electricalBoundaryTreeIteration_positive_actual rule sample
      (fun address => crossing address true) boundaryPositive innerDepth address) outerDepth []
  have shiftIdentity : electricalBoundaryTreeShift rule [] (electricalBoundaryTreeGraft rule innerDepth sample) =
      electricalBoundaryTreeGraft rule innerDepth sample := by funext coordinate; rfl
  simpa only [shiftIdentity, electricalBoundaryTreeGraft, List.nil_append] using weighted

theorem electricalBoundaryTreeIteration_eigenlaw_memLp (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    MemLp (fun sample => (electricalBoundaryTreeIteration rule depth sample:ℝ)) 2
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  have squareIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)^2)
      (scaledProbabilityLaw (growth^depth) law:Measure ℝ≥0) := by
    rw [scaledProbabilityLaw_measure]
    apply (integrable_map_measure (NNReal.continuous_coe.measurable.pow_const 2).aestronglyMeasurable
      (measurable_const.mul measurable_id).aemeasurable).mpr
    simpa only [Function.comp_def, Pi.mul_apply, id_eq, NNReal.coe_mul, mul_pow] using
      secondMoment.const_mul (((growth^depth:ℝ≥0):ℝ)^2)
  have preserving : MeasurePreserving (electricalBoundaryTreeIteration rule depth)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (scaledProbabilityLaw (growth^depth) law:Measure ℝ≥0) :=
    ⟨electricalBoundaryTreeIteration_measurable rule depth,
      (electricalBoundaryTreeIteration_law rule p positive belowOne fixedPoint law depth).trans
        (congrArg (fun law : ProbabilityMeasure ℝ≥0 => (law:Measure ℝ≥0))
          (electricalOutputLaw_iterate_eigenlaw rule p positive belowOne fixedPoint law growth eigenlaw depth))⟩
  exact (memLp_two_iff_integrable_sq
    (NNReal.continuous_coe.measurable.comp (electricalBoundaryTreeIteration_measurable rule depth)).aestronglyMeasurable).mpr
    (preserving.integrable_comp_of_integrable squareIntegrable)

theorem electricalBoundaryTreeIteration_add_condExp_marks_prefix (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (outerDepth innerDepth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)[
      fun sample => (electricalBoundaryTreeIteration rule ((outerDepth+1)+innerDepth) sample:ℝ) |
        (inferInstance : MeasurableSpace
          ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < outerDepth+1} → Configuration rule.edges)).comap
          (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
            fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < outerDepth+1} =>
              (sample coordinate.val).1)] =ᵐ[
        electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
        fun sample => (growth:ℝ)^innerDepth * electricalBoundaryGenerationMean rule law outerDepth
          (fun coordinate => (sample coordinate).1) := by
  let response (data :
      ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < outerDepth+1} → Configuration rule.edges) ×
        (Fin (rule.generation outerDepth).edges → ℝ≥0)) : ℝ :=
    electricalCell (rule.generation outerDepth).network
      (markedGenerationConfiguration rule (innovationPrefixFill rule (outerDepth+1) data.1) outerDepth [] true)
      (fun edge => (data.2 edge:ℝ))
  have responseMeasurable : Measurable response :=
    (NNReal.continuous_coe.comp (electricalCellNNReal_joint_continuous
      (rule.generation outerDepth).network)).measurable.comp
      (((markedGenerationConfiguration_measurable rule outerDepth [] true).comp
        ((innovationPrefixFill_measurable rule (outerDepth+1)).comp measurable_fst)).prodMk measurable_snd)
  have responseEquality : (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      response ((fun coordinate => (sample coordinate.val).1),
        fun leaf => electricalBoundaryTreeIteration rule innerDepth
          (electricalBoundaryTreeShift rule (generationEdgeAddress rule outerDepth leaf) sample))) =ᵐ[
        electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
        fun sample => (electricalBoundaryTreeIteration rule ((outerDepth+1)+innerDepth) sample:ℝ) := by
    have weighted := electricalBoundaryTreeIteration_add_weighted_ae rule p positive belowOne fixedPoint law lawPositive
      outerDepth innerDepth
    filter_upwards [weighted] with sample weighted
    dsimp only [response]
    rw [markedGenerationConfiguration_prefix_factor rule (fun coordinate => (sample coordinate).1) outerDepth true]
    exact weighted.symm
  have responseIntegrable := ((electricalBoundaryTreeIteration_eigenlaw_memLp rule p positive belowOne fixedPoint
    law secondMoment growth eigenlaw ((outerDepth+1)+innerDepth)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).congr
      responseEquality.symm
  have independent := electricalBoundaryTree_marks_prefix_subtrees_independent rule p positive belowOne fixedPoint law
    (generationEdgeAddress rule outerDepth) (generationEdgeAddress_injective rule outerDepth)
    (outerDepth+1) (generationEdgeAddress_length rule outerDepth)
  have iterationMeasurable : Measurable (fun children : Fin (rule.generation outerDepth).edges →
      ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) =>
      fun leaf => electricalBoundaryTreeIteration rule innerDepth (children leaf)) :=
    measurable_pi_lambda _ (fun leaf =>
      (electricalBoundaryTreeIteration_measurable rule innerDepth).comp (measurable_pi_apply leaf))
  have independentOutputs := independent.comp measurable_id iterationMeasurable
  have conditional := independent_pair_condExp_eq_integral
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < outerDepth+1} =>
        (sample coordinate.val).1)
    (fun sample leaf => electricalBoundaryTreeIteration rule innerDepth
      (electricalBoundaryTreeShift rule (generationEdgeAddress rule outerDepth leaf) sample))
    (by fun_prop)
    (measurable_pi_lambda _ (fun leaf => (electricalBoundaryTreeIteration_measurable rule innerDepth).comp
      (electricalBoundaryTreeShift_measurable rule (generationEdgeAddress rule outerDepth leaf))))
    independentOutputs response responseMeasurable.stronglyMeasurable responseIntegrable
  rw [electricalBoundaryTree_frontier_iteration_map] at conditional
  refine (condExp_congr_ae responseEquality).symm.trans ?_
  filter_upwards [conditional] with sample conditional
  dsimp only [response] at conditional
  rw [markedGenerationConfiguration_prefix_factor rule (fun coordinate => (sample coordinate).1) outerDepth true] at conditional
  simp_rw [electricalOutputLaw_iterate_eigenlaw rule p positive belowOne fixedPoint law growth eigenlaw innerDepth] at conditional
  exact conditional.trans (electricalBoundaryGenerationMean_scaled rule law (growth^innerDepth) outerDepth
    (fun coordinate => (sample coordinate).1))

end
end IGSIII34.Percolation
