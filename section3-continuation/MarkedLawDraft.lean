import IGSIII34.Percolation.ElectricalTree
import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Chemical.Substitution IGSIII.Probability

theorem marked_configuration_law (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    (independentInnovationLaw rule parameter positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth address opened) =
      (finiteWeightPMF ((rule.generation depth).network.conditionalCellWeight parameter opened)
        ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le belowOne.le opened)
        ((rule.generation depth).network.sum_conditionalCellWeight parameter
          (by rwa [rule.generation_fixed_point parameter fixedPoint])
          (by rwa [rule.generation_fixed_point parameter fixedPoint]) opened)).toMeasure := by
  calc
    _ = (Rule.ConfigurationHistory.law rule parameter positive belowOne fixedPoint opened depth).map
        (Rule.ConfigurationHistory.latest rule depth) := by
      rw [← independentInnovationLaw_history_marginal rule parameter positive belowOne fixedPoint depth address opened]
      have historyMeasurable : Measurable (fun marks => Rule.ConfigurationHistory.ofFine rule depth
          (markedGenerationConfiguration rule marks depth address opened)) :=
        (measurable_of_countable _).comp (markedGenerationConfiguration_measurable rule depth address opened)
      rw [Measure.map_map (measurable_of_countable (Rule.ConfigurationHistory.latest rule depth)) historyMeasurable]
      congr 1
      funext marks
      rw [Function.comp_apply, Rule.ConfigurationHistory.latest_ofFine]
    _ = _ := by
      rw [Rule.ConfigurationHistory.law]
      apply finite_weight_observable_map
      intro response
      simpa only [Rule.ConfigurationHistory.latest_ofFine] using
        Rule.ConfigurationHistory.joint_observable_law rule parameter positive belowOne fixedPoint opened depth
          (fun history => response (Rule.ConfigurationHistory.latest rule depth history))

end
end IGSIII34.Percolation
