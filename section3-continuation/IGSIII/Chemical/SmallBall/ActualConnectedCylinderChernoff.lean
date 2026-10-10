import IGSIII.Chemical.SmallBall.ConnectedCylinderChernoff
import IGSIII.Chemical.SmallBall.ChemicalTransferPairedBarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution Set IGSIII.Probability
open scoped BigOperators ENNReal

noncomputable section

theorem selected_good_count_measurable
    {State Index Sample : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [Fintype Index] [MeasurableSpace Sample]
    (selected : State → Finset Index) (good : Set Sample) (goodMeasurable : MeasurableSet good) :
    Measurable (fun input : State × (Index → Sample) =>
      ∑ index ∈ selected input.1, good.indicator (fun _ => (1 : ℝ)) (input.2 index)) := by
  apply measurable_from_prod_countable_right
  intro state
  change Measurable (fun samples : Index → Sample => ∑ index ∈ selected state, good.indicator (fun _ => (1 : ℝ)) (samples index))
  simpa only [Function.comp_def] using Finset.measurable_sum (selected state) (fun index _ =>
    ((measurable_const : Measurable (fun _ : Sample => (1 : ℝ))).indicator goodMeasurable).comp (measurable_pi_apply index))

theorem conditioned_selected_good_count_lower_tail
    {State Index Sample : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [Fintype Index] [DecidableEq Index] [MeasurableSpace Sample]
    (weight : State → ℝ) (weightNonnegative : ∀ state, 0 ≤ weight state) (normalized : ∑ state, weight state = 1)
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (good : Set Sample) (goodMeasurable : MeasurableSet good)
    (selected : State → Finset Index) (threshold : ℝ) :
    ((finiteWeightPMF weight weightNonnegative normalized).toMeasure.prod
      (Measure.pi (fun _ : Index => μ))).real
      {input | threshold ≤ ((selected input.1).card : ℝ) ∧
        (∑ index ∈ selected input.1, good.indicator (fun _ => (1 : ℝ)) (input.2 index)) <
          μ.real good / 2 * (selected input.1).card} ≤
      Real.exp (-μ.real good * ((1 / 2 : ℝ) - Real.exp (-1)) * threshold) := by
  have countMeasurable := selected_good_count_measurable selected good goodMeasurable
  have cardinalityMeasurable : Measurable (fun input : State × (Index → Sample) => ((selected input.1).card : ℝ)) :=
    (measurable_of_countable (fun state : State => ((selected state).card : ℝ))).comp measurable_fst
  have eventMeasurable : MeasurableSet {input : State × (Index → Sample) |
      threshold ≤ ((selected input.1).card : ℝ) ∧
      (∑ index ∈ selected input.1, good.indicator (fun _ => (1 : ℝ)) (input.2 index)) <
        μ.real good / 2 * (selected input.1).card} :=
    (measurableSet_le measurable_const cardinalityMeasurable).inter
      (measurableSet_lt countMeasurable (cardinalityMeasurable.const_mul _))
  rw [finiteWeight_prod_event_real weight weightNonnegative normalized _ _ eventMeasurable]
  calc
    _ ≤ ∑ state, weight state * Real.exp (-μ.real good * ((1 / 2 : ℝ) - Real.exp (-1)) * threshold) := by
      apply Finset.sum_le_sum
      intro state _
      apply mul_le_mul_of_nonneg_left _ (weightNonnegative state)
      by_cases large : threshold ≤ ((selected state).card : ℝ)
      · simp only [Set.mem_setOf_eq, large, true_and]
        exact (independent_good_count_lower_tail μ good goodMeasurable (selected state)).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left large
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr measureReal_nonneg) bernoulli_lower_tail_exponent_positive.le)))
      · simp only [Set.mem_setOf_eq, large, false_and, Set.setOf_false, measureReal_empty]
        exact Real.exp_nonneg _
    _ = _ := by rw [← Finset.sum_mul, normalized, one_mul]

def connectedCylinderIndices {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Finset (Fin edges) :=
  Finset.univ.filter (fun edge => network.childState .connected configuration edge = some .connected)

theorem connectedCylinderIndices_card {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    (connectedCylinderIndices network configuration).card = network.liveCount .connected .connected configuration := rfl

noncomputable def goodConnectedCylinderCount (rule : Rule)
    (good : Set ((List (Fin rule.edges) × Bool) → Configuration rule.edges))
    (depth : ℕ) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  ∑ edge ∈ connectedCylinderIndices (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true),
    good.indicator (fun _ => (1 : ℝ)) (innovationTreeShift rule (generationEdgeAddress rule depth edge) marks)

theorem actual_connected_good_count_lower_tail
    (rule : Rule) (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (good : Set ((List (Fin rule.edges) × Bool) → Configuration rule.edges)) (goodMeasurable : MeasurableSet good)
    (depth : ℕ) (threshold : ℝ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | threshold ≤ ((rule.generation depth).network.liveCount .connected .connected
          (markedGenerationConfiguration rule marks depth [] true) : ℝ) ∧
        goodConnectedCylinderCount rule good depth marks <
          (independentInnovationLaw rule p positive lessOne fixedPoint).real good / 2 *
            (rule.generation depth).network.liveCount .connected .connected (markedGenerationConfiguration rule marks depth [] true)} ≤
      Real.exp (-(independentInnovationLaw rule p positive lessOne fixedPoint).real good *
        ((1 / 2 : ℝ) - Real.exp (-1)) * threshold) := by
  let event : Set (Configuration (rule.generation depth).edges ×
      (Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges))) :=
    {input | threshold ≤ ((connectedCylinderIndices (rule.generation depth).network input.1).card : ℝ) ∧
      (∑ edge ∈ connectedCylinderIndices (rule.generation depth).network input.1,
        good.indicator (fun _ => (1 : ℝ)) (input.2 edge)) <
          (independentInnovationLaw rule p positive lessOne fixedPoint).real good / 2 *
            (connectedCylinderIndices (rule.generation depth).network input.1).card}
  have cardinalityMeasurable : Measurable (fun input : Configuration (rule.generation depth).edges ×
      (Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges)) =>
        ((connectedCylinderIndices (rule.generation depth).network input.1).card : ℝ)) :=
    (measurable_of_countable (fun configuration : Configuration (rule.generation depth).edges =>
      ((connectedCylinderIndices (rule.generation depth).network configuration).card : ℝ))).comp measurable_fst
  have eventMeasurable : MeasurableSet event :=
    (measurableSet_le measurable_const cardinalityMeasurable).inter
      (measurableSet_lt (selected_good_count_measurable _ good goodMeasurable) (cardinalityMeasurable.const_mul _))
  have jointMeasurable : Measurable (fun marks =>
      (markedGenerationConfiguration rule marks depth [] true,
        fun edge => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks)) :=
    (markedGenerationConfiguration_measurable rule depth [] true).prodMk
      (measurable_pi_lambda _ (fun edge => innovationTreeShift_measurable rule (generationEdgeAddress rule depth edge)))
  have law := markedGeneration_leafTrees_conditioned_map rule p positive lessOne fixedPoint depth
  rw [Measure.infinitePi_eq_pi] at law
  have eventEquality : {marks | threshold ≤ ((rule.generation depth).network.liveCount .connected .connected
      (markedGenerationConfiguration rule marks depth [] true) : ℝ) ∧ goodConnectedCylinderCount rule good depth marks <
        (independentInnovationLaw rule p positive lessOne fixedPoint).real good / 2 *
          (rule.generation depth).network.liveCount .connected .connected (markedGenerationConfiguration rule marks depth [] true)} =
      (fun marks => (markedGenerationConfiguration rule marks depth [] true,
        fun edge => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks)) ⁻¹' event := rfl
  rw [eventEquality, measureReal_def, ← Measure.map_apply jointMeasurable eventMeasurable, law, ← measureReal_def]
  exact conditioned_selected_good_count_lower_tail _ _ _ _ good goodMeasurable
    (connectedCylinderIndices (rule.generation depth).network) threshold

end
end IGSIII.Chemical.SmallBall