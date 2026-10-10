import IGSIII.Chemical.SmallBall.MeasurePairedBarrier
import IGSIII.Chemical.SmallBall.TransferValue
import IGSIII.Chemical.SubstitutionPaths.WeightedLeafLaw
import IGSIII.Chemical.SubstitutionPaths.MarkedConfigurationLaw
import IGSIII.Chemical.SubstitutionPaths.BlockPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution Set IGSIII.Probability
open scoped BigOperators ENNReal

noncomputable section

theorem paired_shortest_event_measurable {State Edge Sample : Type*} [Fintype Edge] [DecidableEq Edge]
    [MeasurableSpace State] [Countable State] [MeasurableSingletonClass State] [MeasurableSpace Sample]
    (families : State → PathFamily Edge) (first second : Sample → ℝ)
    (firstMeasurable : Measurable first) (secondMeasurable : Measurable second) (scale : ℝ) :
    MeasurableSet {input : State × (Edge → Sample) |
      scale * (families input.1).shortest (fun edge => second (input.2 edge)) <
        (families input.1).shortest (fun edge => first (input.2 edge))} := by
  have firstCost : Measurable (fun input : State × (Edge → Sample) =>
      (input.1, fun edge => first (input.2 edge))) :=
    measurable_fst.prodMk (measurable_pi_lambda _ (fun edge =>
      firstMeasurable.comp ((measurable_pi_apply edge).comp measurable_snd)))
  have secondCost : Measurable (fun input : State × (Edge → Sample) =>
      (input.1, fun edge => second (input.2 edge))) :=
    measurable_fst.prodMk (measurable_pi_lambda _ (fun edge =>
      secondMeasurable.comp ((measurable_pi_apply edge).comp measurable_snd)))
  have firstShortest : Measurable (fun input : State × (Edge → Sample) =>
      (families input.1).shortest (fun edge => first (input.2 edge))) := by
    simpa only [Function.comp_def] using
      (PathFamily.shortest_dispatch_measurable families).comp firstCost
  have secondShortest : Measurable (fun input : State × (Edge → Sample) =>
      (families input.1).shortest (fun edge => second (input.2 edge))) := by
    simpa only [Function.comp_def] using
      (PathFamily.shortest_dispatch_measurable families).comp secondCost
  exact measurableSet_lt (secondShortest.const_mul scale) firstShortest

theorem finiteWeight_prod_event_real {State Sample : Type*} [Fintype State]
    [MeasurableSpace State] [MeasurableSingletonClass State] [MeasurableSpace Sample]
    (weight : State → ℝ) (weightNonnegative : ∀ state, 0 ≤ weight state) (normalized : ∑ state, weight state = 1)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (event : Set (State × Sample)) (eventMeasurable : MeasurableSet event) :
    ((finiteWeightPMF weight weightNonnegative normalized).toMeasure.prod measure).real event =
      ∑ state, weight state * measure.real {sample | (state, sample) ∈ event} := by
  rw [measureReal_def, Measure.prod_apply eventMeasurable, lintegral_fintype]
  simp only [finiteWeightPMF_singleton]
  rw [ENNReal.toReal_sum (fun state _ => ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro state _
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (weightNonnegative state), measureReal_def]
  rw [mul_comm]
  rfl

theorem chemicalTransfer_iterate_paired_comparison_bound (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    {scale ratio : ℝ} (ratioNonnegative : 0 ≤ ratio)
    (pairedIntegrable : Integrable (fun marks => Real.exp (first marks - scale * second marks))
      (independentInnovationLaw rule p positive lessOne fixedPoint))
    (pairedBound : (∫ marks, Real.exp (first marks - scale * second marks)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) (depth : ℕ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | scale * ((chemicalTransfer rule)^[depth + 1] second) marks <
        ((chemicalTransfer rule)^[depth + 1] first) marks} ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
  let event : Set (Configuration (rule.generation depth).edges ×
      (Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges))) :=
    {input | scale * (edgePathFamily (rule.generation depth).network input.1).shortest (fun edge => second (input.2 edge)) <
      (edgePathFamily (rule.generation depth).network input.1).shortest (fun edge => first (input.2 edge))}
  have eventMeasurable : MeasurableSet event :=
    paired_shortest_event_measurable _ _ _ (Lp.stronglyMeasurable first).measurable
      (Lp.stronglyMeasurable second).measurable scale
  have jointMeasurable : Measurable (fun marks =>
      (markedGenerationConfiguration rule marks depth [] true,
        fun edge => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks)) :=
    (markedGenerationConfiguration_measurable rule depth [] true).prodMk
      (measurable_pi_lambda _ (fun edge => innovationTreeShift_measurable rule (generationEdgeAddress rule depth edge)))
  have law := markedGeneration_leafTrees_conditioned_map rule p positive lessOne fixedPoint depth
  rw [Measure.infinitePi_eq_pi] at law
  have eventEquality : {marks | scale * ((chemicalTransfer rule)^[depth + 1] second) marks <
      ((chemicalTransfer rule)^[depth + 1] first) marks} =ᵐ[independentInnovationLaw rule p positive lessOne fixedPoint]
      (fun marks => (markedGenerationConfiguration rule marks depth [] true,
        fun edge => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks)) ⁻¹' event := by
    filter_upwards [chemicalTransfer_iterate_eq_weighted_actual_ae rule classical first p positive lessOne fixedPoint,
      chemicalTransfer_iterate_eq_weighted_actual_ae rule classical second p positive lessOne fixedPoint] with marks firstEquality secondEquality
    have firstRoot := firstEquality depth []
    have secondRoot := secondEquality depth []
    have rootShift : innovationTreeShift rule [] marks = marks := by funext coordinate; rfl
    rw [rootShift] at firstRoot secondRoot
    simp only [List.nil_append] at firstRoot secondRoot
    apply propext
    change (scale * ((chemicalTransfer rule)^[depth + 1] second) marks <
      ((chemicalTransfer rule)^[depth + 1] first) marks) ↔ _
    rw [firstRoot, secondRoot]
    rfl
  have eventLaw : (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | scale * ((chemicalTransfer rule)^[depth + 1] second) marks <
        ((chemicalTransfer rule)^[depth + 1] first) marks} =
      ∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        (Measure.pi (fun _ : Fin (rule.generation depth).edges => independentInnovationLaw rule p positive lessOne fixedPoint)).real
          {children | scale * (edgePathFamily (rule.generation depth).network configuration).shortest (fun edge => second (children edge)) <
            (edgePathFamily (rule.generation depth).network configuration).shortest (fun edge => first (children edge))} := by
    rw [measureReal_congr eventEquality]
    have mapEquality : (independentInnovationLaw rule p positive lessOne fixedPoint).real
        ((fun marks => (markedGenerationConfiguration rule marks depth [] true,
          fun edge => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks)) ⁻¹' event) =
        ((independentInnovationLaw rule p positive lessOne fixedPoint).map
          (fun marks => (markedGenerationConfiguration rule marks depth [] true,
            fun edge => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks))).real event := by
      rw [measureReal_def, measureReal_def, Measure.map_apply jointMeasurable eventMeasurable]
    rw [mapEquality, law, finiteWeight_prod_event_real _ _ _ _ event eventMeasurable]
    rfl
  rw [eventLaw]
  have pointwise (configuration : Configuration (rule.generation depth).edges)
      (crossing : (rule.generation depth).network.crosses configuration = true) :
      (Measure.pi (fun _ : Fin (rule.generation depth).edges => independentInnovationLaw rule p positive lessOne fixedPoint)).real
          {children | scale * (edgePathFamily (rule.generation depth).network configuration).shortest (fun edge => second (children edge)) <
            (edgePathFamily (rule.generation depth).network configuration).shortest (fun edge => first (children edge))} ≤
        ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
    refine (measure_product_shortest_paired_barrier (edgePathFamily (rule.generation depth).network configuration)
      (fun _ => independentInnovationLaw rule p positive lessOne fixedPoint) (fun _ => first) (fun _ => second)
      (fun _ => (Lp.stronglyMeasurable first).measurable) (fun _ => (Lp.stronglyMeasurable second).measurable)
      (parameter := 1) (ratio := ratio) zero_le_one
      (fun _ _ _ _ => by simpa only [one_mul] using pairedIntegrable)
      (fun _ _ _ _ => by simpa only [one_mul] using pairedBound)).trans ?_
    apply path_sum_le_geometric_tail_from_minimum _ _ _ ratioNonnegative (Nat.cast_nonneg _) _ geometricBelowOne
    · intro path membership
      rw [← rule.generation_terminal_distance (classical.connected _) depth]
      exact (edgePathFamily_card_bounds _ (classical.generation depth).simple configuration crossing membership).1
    · intro size
      exact_mod_cast actual_edgePathFamily_length_count rule classical depth size configuration
  have averaged := Finset.sum_le_sum (s := Finset.univ) (fun configuration _ => show
      (rule.generation depth).network.conditionalCellWeight p true configuration *
        (Measure.pi (fun _ : Fin (rule.generation depth).edges => independentInnovationLaw rule p positive lessOne fixedPoint)).real
          {children | scale * (edgePathFamily (rule.generation depth).network configuration).shortest (fun edge => second (children edge)) <
            (edgePathFamily (rule.generation depth).network configuration).shortest (fun edge => first (children edge))} ≤
      (rule.generation depth).network.conditionalCellWeight p true configuration *
        (((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio)) from by
      by_cases crossing : (rule.generation depth).network.crosses configuration = true
      · exact mul_le_mul_of_nonneg_left (pointwise configuration crossing)
          ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
      · simp [conditionalCellWeight, crossing])
  simpa only [← Finset.sum_mul, (rule.generation depth).network.sum_conditionalCellWeight p
    (by rwa [rule.generation_fixed_point p fixedPoint]) (by rwa [rule.generation_fixed_point p fixedPoint]) true, one_mul] using averaged

end
end IGSIII.Chemical.SmallBall
