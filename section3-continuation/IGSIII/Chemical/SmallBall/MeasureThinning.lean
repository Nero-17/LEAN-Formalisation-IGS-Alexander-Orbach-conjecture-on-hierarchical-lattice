import IGSIII.Chemical.SmallBall.ChemicalTransferPairedBarrier
import IGSIII.Chemical.SmallBall.FiniteProbability
import IGSIII.Chemical.SubstitutionPaths.RetentionLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution Set IGSIII.Probability
open scoped BigOperators ENNReal

noncomputable section

theorem measurable_retention_singleton {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure] (retention : Sample → Bool)
    (measurable : Measurable retention) (bit : Bool) :
    (measure.map retention) {bit} =
      ENNReal.ofReal (bitWeight (measure.real {sample | retention sample = true}) bit) := by
  have eventMeasurable : MeasurableSet {sample | retention sample = true} :=
    measurableSet_eq_fun measurable measurable_const
  rw [Measure.map_apply measurable (measurableSet_singleton bit)]
  cases bit with
  | true =>
      simp only [bitWeight, ↓reduceIte]
      rw [ofReal_measureReal]
      rfl
  | false =>
      have fiber : retention ⁻¹' {false} = {sample | retention sample = true}ᶜ := by
        ext sample
        cases retention sample <;> simp
      rw [fiber, ← ofReal_measureReal, measureReal_compl eventMeasurable, probReal_univ]
      rfl

theorem measure_pi_retention_map {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure] (edges : ℕ)
    (retention : Sample → Bool) (measurable : Measurable retention) :
    (Measure.pi (fun _ : Fin edges => measure)).map (fun children edge => retention (children edge)) =
      (finiteWeightPMF (bernoulliWeight (measure.real {sample | retention sample = true}))
        (bernoulliWeight_nonneg measureReal_nonneg measureReal_le_one)
        (sum_bernoulliWeight _)).toMeasure := by
  rw [Measure.pi_map_pi (fun _ => measurable.aemeasurable)]
  apply Measure.ext_of_singleton
  intro configuration
  rw [Measure.pi_singleton, finiteWeightPMF_singleton]
  simp_rw [measurable_retention_singleton measure retention measurable]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rfl
  · intro edge _
    cases configuration edge <;> simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
    · exact sub_nonneg.mpr measureReal_le_one
    · exact measureReal_nonneg

theorem product_retention_crossing_probability {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (retention : Sample → Bool) (measurable : Measurable retention) :
    (Measure.pi (fun _ : Fin edges => measure)).real
      {children | network.crosses (fun edge => configuration edge && retention (children edge)) = true} =
      ∑ retained : Configuration edges, bernoulliWeight (measure.real {sample | retention sample = true}) retained *
        (if network.crosses (fun edge => configuration edge && retained edge) then 1 else 0) := by
  have vectorMeasurable : Measurable (fun children : Fin edges → Sample => fun edge => retention (children edge)) :=
    measurable_pi_lambda _ (fun edge => measurable.comp (measurable_pi_apply edge))
  have eventMeasurable : MeasurableSet
      {retained : Configuration edges | network.crosses (fun edge => configuration edge && retained edge) = true} :=
    (Set.toFinite _).measurableSet
  have equality := Measure.map_apply (μ := Measure.pi (fun _ : Fin edges => measure)) vectorMeasurable eventMeasurable
  have realEquality := congrArg ENNReal.toReal equality
  rw [measure_pi_retention_map measure edges retention measurable, ← measureReal_def, finiteWeight_event] at realEquality
  simpa only [measureReal_def, Set.preimage_setOf_eq, Bool.coe_iff_coe] using realEquality.symm

theorem conditioned_product_retention_crossing_probability {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (p : ℝ) (fixedPoint : network.reliability p = p)
    (retention : Sample → Bool) (measurable : Measurable retention) :
    (∑ configuration : Configuration edges, network.conditionalCellWeight p true configuration *
      (Measure.pi (fun _ : Fin edges => measure)).real
        {children | network.crosses (fun edge => configuration edge && retention (children edge)) = true}) =
      thinningMap network p (measure.real {sample | retention sample = true}) := by
  simp_rw [product_retention_crossing_probability measure network _ retention measurable]
  exact conditional_independent_retention_crossing network p fixedPoint _

theorem actual_tree_retention_crossing_probability (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (retention : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool)
    (measurable : Measurable retention) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | rule.network.crosses (fun edge => marks ([], true) edge &&
        retention (innovationTreeShift rule [edge] marks)) = true} =
      thinningMap rule.network p
        ((independentInnovationLaw rule p positive lessOne fixedPoint).real {marks | retention marks = true}) := by
  let event : Set (Configuration rule.edges ×
      (Fin rule.edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges))) :=
    {input | rule.network.crosses (fun edge => input.1 edge && retention (input.2 edge)) = true}
  have retainedMeasurable : Measurable (fun input : Configuration rule.edges ×
      (Fin rule.edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges)) =>
      (input.1, fun edge => retention (input.2 edge))) :=
    measurable_fst.prodMk (measurable_pi_lambda _ (fun edge =>
      measurable.comp ((measurable_pi_apply edge).comp measurable_snd)))
  have eventMeasurable : MeasurableSet event := by
    have finiteEvent : MeasurableSet {input : Configuration rule.edges × Configuration rule.edges |
      rule.network.crosses (fun edge => input.1 edge && input.2 edge) = true} := (Set.toFinite _).measurableSet
    exact finiteEvent.preimage retainedMeasurable
  have jointMeasurable : Measurable (fun marks =>
      (marks ([], true), fun edge => innovationTreeShift rule [edge] marks)) :=
    (measurable_pi_apply ([], true)).prodMk
      (measurable_pi_lambda _ (fun edge => innovationTreeShift_measurable rule [edge]))
  have law := markedGeneration_leafTrees_conditioned_map rule p positive lessOne fixedPoint 0
  simp only [markedGenerationConfiguration, generationEdgeAddress, Rule.generation,
    Measure.infinitePi_eq_pi] at law
  have mapEquality := Measure.map_apply (μ := independentInnovationLaw rule p positive lessOne fixedPoint)
    jointMeasurable eventMeasurable
  have realEquality := congrArg ENNReal.toReal mapEquality
  rw [law, ← measureReal_def, finiteWeight_prod_event_real _ _ _ _ event eventMeasurable] at realEquality
  change ((independentInnovationLaw rule p positive lessOne fixedPoint)
    ((fun marks => (marks ([], true), fun edge => innovationTreeShift rule [edge] marks)) ⁻¹' event)).toReal = _
  rw [← realEquality]
  exact conditioned_product_retention_crossing_probability
    (independentInnovationLaw rule p positive lessOne fixedPoint) rule.network p fixedPoint retention measurable

end
end IGSIII.Chemical.SmallBall
