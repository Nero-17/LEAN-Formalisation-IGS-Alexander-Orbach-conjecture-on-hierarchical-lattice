import IGSIII34.Percolation.MarkedLaw
import IGSIII34.Percolation.ElectricalMeasurability
import IGSIII34.Percolation.MeanResistance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Chemical.Substitution IGSIII.Probability

theorem marked_observable_integral (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    (∫ marks, response (markedGenerationConfiguration rule marks depth address opened)
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) =
      ∑ configuration, (rule.generation depth).network.conditionalCellWeight parameter opened configuration *
        response configuration := by
  rw [← integral_map_of_stronglyMeasurable
    (markedGenerationConfiguration_measurable rule depth address opened)
    (measurable_of_countable response).stronglyMeasurable,
    marked_configuration_law, PMF.integral_eq_sum]
  simp only [finiteWeightPMF_apply, ENNReal.toReal_ofReal
    ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le belowOne.le opened _), smul_eq_mul]

theorem marked_observable_integrable (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    Integrable (fun marks => response (markedGenerationConfiguration rule marks depth address opened))
      (independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
  apply (integrable_map_measure (measurable_of_countable response).aestronglyMeasurable
    (markedGenerationConfiguration_measurable rule depth address opened).aemeasurable).mp
  rw [marked_configuration_law rule parameter positive belowOne fixedPoint depth address opened]
  exact Integrable.of_finite

theorem electricalIteration_real_power_integrable (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges)) (order : ℝ) :
    Integrable (fun marks => (electricalIteration rule marks depth address) ^ order)
      (independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
  cases depth with
  | zero => simpa only [electricalIteration, Real.one_rpow] using
      (integrable_const (μ := independentInnovationLaw rule parameter positive belowOne fixedPoint) (1 : ℝ))
  | succ depth =>
      apply (marked_observable_integrable rule parameter positive belowOne fixedPoint depth address true
        (fun configuration => (unitConfigurationResistance (rule.generation depth).network configuration) ^ order)).congr
      filter_upwards [independentInnovationLaw_crosses rule parameter positive belowOne fixedPoint] with marks crossing
      rw [markedGeneration_resistance_eq_iteration rule marks crossing]

theorem electricalIteration_mean_eq_conditionalMeanResistance (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (∫ marks, electricalIteration rule marks (depth + 1) address
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) =
      conditionalMeanResistance (rule.generation depth).network parameter := by
  calc
    _ = ∫ marks, unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth address true)
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
      apply integral_congr_ae
      filter_upwards [independentInnovationLaw_crosses rule parameter positive belowOne fixedPoint] with marks crossing
      exact (markedGeneration_resistance_eq_iteration rule marks crossing depth address).symm
    _ = _ := by
      rw [marked_observable_integral rule parameter positive belowOne fixedPoint depth address true]
      unfold conditionalMeanResistance Universality.FiniteNetwork.expectation
        Universality.FiniteNetwork.conditionalCellWeight
      simp only [Bool.true_eq, ↓reduceIte]
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro configuration _
      by_cases crosses : (rule.generation depth).network.crosses configuration = true
      · simp only [crosses, Bool.true_eq, ↓reduceIte, unitConfigurationResistance, electricalCell,
          configurationResistance]
        ring
      · simp only [crosses, Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero]

theorem electricalIteration_mean_lower_bound (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    deriv rule.network.reliability parameter ^ (depth + 1) ≤
      ∫ marks, electricalIteration rule marks (depth + 1) address
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
  rw [electricalIteration_mean_eq_conditionalMeanResistance rule parameter positive belowOne fixedPoint]
  exact generation_conditionalMeanResistance_lower_bound rule positive belowOne.le fixedPoint depth

end
end IGSIII34.Percolation
