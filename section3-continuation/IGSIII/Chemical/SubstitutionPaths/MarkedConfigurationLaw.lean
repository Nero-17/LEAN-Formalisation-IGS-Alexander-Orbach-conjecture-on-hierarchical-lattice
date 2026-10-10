import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders
import IGSIII.Chemical.SubstitutionPaths.WeightedLeafLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability
open scoped BigOperators ENNReal

theorem independentInnovationLaw_marked_configuration_marginal (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth address opened) =
      (finiteWeightPMF ((rule.generation depth).network.conditionalCellWeight p opened)
        ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le opened)
        ((rule.generation depth).network.sum_conditionalCellWeight p
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint]) opened)).toMeasure := by
  calc
    _ = (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint opened depth).map
        (Rule.ConfigurationHistory.latest rule depth) := by
      rw [← independentInnovationLaw_history_marginal rule p positive lessOne fixedPoint depth address opened]
      have historyMeasurable : Measurable (fun marks => Rule.ConfigurationHistory.ofFine rule depth
          (markedGenerationConfiguration rule marks depth address opened)) :=
        (measurable_of_countable _).comp (markedGenerationConfiguration_measurable rule depth address opened)
      rw [Measure.map_map (measurable_of_countable (Rule.ConfigurationHistory.latest rule depth))
        historyMeasurable]
      congr 1
      funext marks
      rw [Function.comp_apply, Rule.ConfigurationHistory.latest_ofFine]
    _ = _ := by
      rw [Rule.ConfigurationHistory.law]
      apply finite_weight_observable_map
      intro response
      simpa only [Rule.ConfigurationHistory.latest_ofFine] using
        Rule.ConfigurationHistory.joint_observable_law rule p positive lessOne fixedPoint opened depth
          (fun history => response (Rule.ConfigurationHistory.latest rule depth history))

theorem independentInnovationLaw_marked_lintegral (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ≥0∞) :
    (∫⁻ marks, response (markedGenerationConfiguration rule marks depth address opened)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) =
        ∑ configuration, ENNReal.ofReal ((rule.generation depth).network.conditionalCellWeight p opened configuration) *
          response configuration := by
  rw [← lintegral_map (measurable_of_countable _) (markedGenerationConfiguration_measurable rule depth address opened),
    independentInnovationLaw_marked_configuration_marginal, lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finiteWeightPMF_apply, mul_comm]

theorem markedGeneration_leafTrees_conditioned_map (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => (markedGenerationConfiguration rule marks depth [] true,
          fun leaf => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) =
      (finiteWeightPMF ((rule.generation depth).network.conditionalCellWeight p true)
        ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true)
        ((rule.generation depth).network.sum_conditionalCellWeight p
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint]) true)).toMeasure.prod
        (Measure.infinitePi (fun _ : Fin (rule.generation depth).edges =>
          independentInnovationLaw rule p positive lessOne fixedPoint)) := by
  rw [markedGeneration_leafTrees_map, independentInnovationLaw_marked_configuration_marginal]

end IGSIII.Chemical.Substitution
