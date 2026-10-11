import Universality.Percolation.InfiniteConfigurationLaw
import Universality.Percolation.RandomEIGS
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem integral_law (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory n → ℝ) :
    ∫ history, observable history ∂law rule p hp hp' hfixed opened n =
      ∑ history, recursiveWeight rule p opened n history * observable history := by
  rw [law, PMF.integral_eq_sum]
  simp only [finiteWeightPMF_apply, ENNReal.toReal_ofReal
    (recursiveWeight_nonneg rule p hp hp' hfixed opened n _), smul_eq_mul]

/-- Every finite-history observable on the common space has the original
conditional Bernoulli expectation on the actual finest graph. -/
theorem integral_infiniteLaw (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory n → ℝ) :
    ∫ path, observable (path n) ∂infiniteLaw rule p hp hp' hfixed opened =
      ∑ fine, (rule.generation n).network.conditionalCellWeight p opened fine *
        observable (ofFine rule n fine) := by
  rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply n)
    (measurable_of_countable observable).stronglyMeasurable,
    infiniteLaw_marginal, integral_law]
  exact joint_observable_law rule p hp hp' hfixed opened n observable

theorem infiniteLaw_recursiveLabels (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂infiniteLaw rule p hp hp' hfixed opened, ∀ n,
      recursiveLabels rule n (path n) = globalLabels rule n (path n) := by
  filter_upwards [infiniteLaw_coherent rule p hp hp' hfixed opened] with path hpath
  exact fun n => recursiveLabels_eq_globalLabels rule n (path n) (hpath n)

/-- The infinite process retains the full labelled EIGS law, including joint
observables across levels and dependence among siblings. -/
theorem infinite_randomEIGS_joint_law (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (observable : rule.LabelHistory n → ℝ) :
    ∫ path, observable (recursiveLabels rule n (path n))
        ∂infiniteLaw rule p hp hp' hfixed true =
      ∑ fine, (rule.generation n).network.conditionalCellWeight p true fine *
        observable (globalLabels rule n (ofFine rule n fine)) := by
  rw [integral_infiniteLaw rule p hp hp' hfixed true n
    (fun history => observable (recursiveLabels rule n history))]
  apply Finset.sum_congr rfl
  intro fine _
  rw [recursiveLabels_eq_globalLabels rule n _
    ((coherent_iff_ofFine rule n _).mpr (by rw [latest_ofFine]))]

end
end Universality.Rule.ConfigurationHistory
