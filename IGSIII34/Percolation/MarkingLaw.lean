import IGSIII34.Probability.FiniteMarking
import IGSIII34.Percolation.ThinningWeights
import IGSIII34.Percolation.LawMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped NNReal ENNReal

theorem connectedConfigurationLaw_singleton (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (configuration : Configuration rule.edges) :
    (connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _) {configuration} =
      ENNReal.ofReal (rule.network.conditionalCellWeight parameter true configuration) := by
  change (finiteWeightPMF (rule.network.conditionalCellWeight parameter true)
    (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le true)
    (rule.network.sum_conditionalCellWeight parameter (by rwa [fixedPoint])
      (by rwa [fixedPoint]) true)).toMeasure {configuration} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finiteWeightPMF_apply]

theorem conditioned_iid_marking_lintegral (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) (mark : ℝ≥0 → Bool) (markMeasurable : Measurable mark) :
    (∫⁻ data : Configuration rule.edges × (Fin rule.edges → ℝ≥0),
      (if rule.network.crosses (fun edge => data.1 edge && mark (data.2 edge)) then 1 else 0 : ℝ≥0∞)
      ∂(electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _)) =
        ENNReal.ofReal (rule.network.reliability
          (parameter * ((law : Measure ℝ≥0) {value | mark value = true}).toReal) / parameter) := by
  have jointMarking : Measurable (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) =>
      (data.1, fun edge => mark (data.2 edge))) :=
    measurable_fst.prodMk (measurable_pi_lambda _ (fun edge =>
      markMeasurable.comp ((measurable_pi_apply edge).comp measurable_snd)))
  have responseMeasurable : Measurable (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) =>
      (if rule.network.crosses (fun edge => data.1 edge && mark (data.2 edge)) then 1 else 0 : ℝ≥0∞)) :=
    (measurable_of_finite (fun pair : Configuration rule.edges × Configuration rule.edges =>
      (if rule.network.crosses (fun edge => pair.1 edge && pair.2 edge) then 1 else 0 : ℝ≥0∞))).comp jointMarking
  change (∫⁻ data : Configuration rule.edges × (Fin rule.edges → ℝ≥0),
    (if rule.network.crosses (fun edge => data.1 edge && mark (data.2 edge)) then 1 else 0 : ℝ≥0∞)
    ∂((connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _).prod
      (Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0))))) = _
  rw [lintegral_prod _ responseMeasurable.aemeasurable]
  have innerIdentity (configuration : Configuration rule.edges) :
      (∫⁻ input : Fin rule.edges → ℝ≥0,
        (if rule.network.crosses (fun edge => configuration edge && mark (input edge)) then 1 else 0 : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0))) =
          ENNReal.ofReal (∑ marking, bernoulliWeight
            (((law : Measure ℝ≥0) {value | mark value = true}).toReal) marking *
              (if rule.network.crosses (fun edge => configuration edge && marking edge) then 1 else 0 : ℝ)) := by
    convert IGSIII34.Probability.iid_bool_marking_lintegral law mark markMeasurable
      (fun marking => (if rule.network.crosses (fun edge => configuration edge && marking edge) then 1 else 0 : ℝ))
      (fun marking => by split_ifs <;> positivity) using 1
    congr 1
    funext input
    split_ifs <;> simp
  simp_rw [innerIdentity]
  rw [lintegral_fintype]
  have markingBounds := IGSIII34.Probability.bool_marking_probability_bounds law mark
  have innerNonnegative (configuration : Configuration rule.edges) :
      0 ≤ ∑ marking, bernoulliWeight (((law : Measure ℝ≥0) {value | mark value = true}).toReal) marking *
        (if rule.network.crosses (fun edge => configuration edge && marking edge) then 1 else 0 : ℝ) :=
    Finset.sum_nonneg (fun marking _ => mul_nonneg
      (bernoulliWeight_nonneg markingBounds.1 markingBounds.2 marking) (by split_ifs <;> positivity))
  have thinning := conditioned_bernoulli_thinning_split rule.network parameter
    (((law : Measure ℝ≥0) {value | mark value = true}).toReal)
  rw [fixedPoint] at thinning
  rw [← thinning]
  rw [ENNReal.ofReal_sum_of_nonneg (fun configuration _ => mul_nonneg
    (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le true configuration)
    (innerNonnegative configuration))]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [connectedConfigurationLaw_singleton,
    ENNReal.ofReal_mul (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le true configuration), mul_comm]

end
end IGSIII34.Percolation
