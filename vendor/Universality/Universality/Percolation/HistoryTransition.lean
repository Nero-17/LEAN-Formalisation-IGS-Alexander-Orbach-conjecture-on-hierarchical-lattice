import Universality.Percolation.MultilevelLaw
import Universality.Probability.FiniteWeightMeasure

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators

instance measurableSpace (rule : Rule) : (n : ℕ) →
    MeasurableSpace (rule.ConfigurationHistory n)
  | 0 => inferInstanceAs (MeasurableSpace (Configuration rule.edges))
  | n + 1 => by
    letI := measurableSpace rule n
    exact inferInstanceAs (MeasurableSpace (rule.ConfigurationHistory n ×
      Configuration (rule.generation (n + 1)).edges))

instance measurableSingletonClass (rule : Rule) : (n : ℕ) →
    MeasurableSingletonClass (rule.ConfigurationHistory n)
  | 0 => inferInstanceAs (MeasurableSingletonClass (Configuration rule.edges))
  | n + 1 => by
    letI := measurableSingletonClass rule n
    exact inferInstanceAs (MeasurableSingletonClass (rule.ConfigurationHistory n ×
      Configuration (rule.generation (n + 1)).edges))

def refinementWeight (rule : Rule) (p : ℝ) (n : ℕ)
    (coarse : Configuration (rule.generation n).edges)
    (fine : Configuration (rule.generation (n + 1)).edges) : ℝ :=
  ∏ e, rule.network.conditionalCellWeight p (coarse e)
    (substitutionConfigurationEquiv.symm fine e)

theorem refinementWeight_nonneg (rule : Rule) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) (coarse : Configuration (rule.generation n).edges)
    (fine : Configuration (rule.generation (n + 1)).edges) :
    0 ≤ refinementWeight rule p n coarse fine :=
  Finset.prod_nonneg (fun _ _ => rule.network.conditionalCellWeight_nonneg hp hp' _ _)

theorem sum_refinementWeight (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ)
    (coarse : Configuration (rule.generation n).edges) :
    ∑ fine, refinementWeight rule p n coarse fine = 1 := by
  classical
  unfold refinementWeight
  change (∑ fine : Configuration ((rule.generation n).edges * rule.edges),
    ∏ e, rule.network.conditionalCellWeight p (coarse e)
      (substitutionConfigurationEquiv.symm fine e)) = 1
  rw [← Equiv.sum_comp substitutionConfigurationEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [← Fintype.prod_sum]
  have hcell (e : Fin (rule.generation n).edges) :
      ∑ cell, rule.network.conditionalCellWeight p (coarse e) cell = 1 :=
    rule.network.sum_conditionalCellWeight p (by rwa [hfixed]) (by rwa [hfixed]) _
  simp_rw [hcell]
  simp

def extensionWeight (rule : Rule) (p : ℝ) (n : ℕ)
    (history : rule.ConfigurationHistory n) (next : rule.ConfigurationHistory (n + 1)) : ℝ :=
  if next.1 = history then refinementWeight rule p n (latest rule n history) next.2 else 0

theorem extensionWeight_nonneg (rule : Rule) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) (history : rule.ConfigurationHistory n) (next : rule.ConfigurationHistory (n + 1)) :
    0 ≤ extensionWeight rule p n history next := by
  unfold extensionWeight
  split
  · exact refinementWeight_nonneg rule p hp hp' _ _ _
  · exact le_rfl

theorem sum_extensionWeight (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ) (history : rule.ConfigurationHistory n) :
    ∑ next, extensionWeight rule p n history next = 1 := by
  classical
  change (∑ next : rule.ConfigurationHistory n × Configuration (rule.generation (n + 1)).edges,
    if next.1 = history then refinementWeight rule p n (latest rule n history) next.2 else 0) = 1
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  exact sum_refinementWeight rule p hp hp' hfixed n _

theorem recursiveWeight_extension (rule : Rule) (p : ℝ) (opened : Bool) (n : ℕ)
    (next : rule.ConfigurationHistory (n + 1)) :
    (∑ history, recursiveWeight rule p opened n history * extensionWeight rule p n history next) =
      recursiveWeight rule p opened (n + 1) next := by
  classical
  simp [extensionWeight, mul_ite, recursiveWeight, refinementWeight]

def law (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ) :
    Measure (rule.ConfigurationHistory n) :=
  (finiteWeightPMF (recursiveWeight rule p opened n)
    (recursiveWeight_nonneg rule p hp hp' hfixed opened n)
    (sum_recursiveWeight rule p hp hp' hfixed opened n)).toMeasure

instance law_probability (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ) :
    IsProbabilityMeasure (law rule p hp hp' hfixed opened n) := by
  unfold law
  infer_instance

def transition (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ) :
    Kernel (rule.ConfigurationHistory n) (rule.ConfigurationHistory (n + 1)) :=
  finiteWeightKernel (extensionWeight rule p n) (extensionWeight_nonneg rule p hp.le hp'.le n)
    (sum_extensionWeight rule p hp hp' hfixed n)

instance transition_markov (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ) :
    IsMarkovKernel (transition rule p hp hp' hfixed n) := by
  unfold transition
  infer_instance

theorem transition_law (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ) :
    transition rule p hp hp' hfixed n ∘ₘ law rule p hp hp' hfixed opened n =
      law rule p hp hp' hfixed opened (n + 1) := by
  apply finiteWeightKernel_comp
  exact recursiveWeight_extension rule p opened n

end
end Universality.Rule.ConfigurationHistory
