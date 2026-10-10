import IGSIII.Mass.ComponentBoundaryLaw
import IGSIII.Mass.ComponentFinitePartition

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

def componentEmpiricalWordWeight (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool))
    (word : Fin age → (Fin rule.edges × Bool)) : ℝ :=
  if 0 < markedComponentVertexMass rule marks (fine + age) [] then
    (markedComponentVertexMass rule marks fine (List.ofFn word) +
      if word = fallback then componentFrontierVertexMass rule marks age [] else 0) /
        markedComponentVertexMass rule marks (fine + age) []
  else if word = fallback then 1 else 0

theorem componentEmpiricalWordWeight_nonnegative (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool)) :
    0 ≤ componentEmpiricalWordWeight rule marks fine age fallback word := by
  unfold componentEmpiricalWordWeight
  split_ifs with positive _ _
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) (componentFrontierVertexMass_nonnegative rule marks age [])) positive.le
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) le_rfl) positive.le
  · exact zero_le_one
  · exact le_rfl

theorem componentEmpiricalWordWeight_sum (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    ∑ word, componentEmpiricalWordWeight rule marks fine age fallback word = 1 := by
  classical
  unfold componentEmpiricalWordWeight
  by_cases positive : 0 < markedComponentVertexMass rule marks (fine + age) []
  · simp only [positive, if_true, ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have partition := actual_component_finite_partition rule marks crossing fine age []
    simp only [List.nil_append] at partition
    rw [add_comm, ← partition, div_self positive.ne']
  · simp only [positive, if_false]
    simp

/-- The actual finite component counts define a probability law after assigning
the finitely many older planting vertices to one fixed frontier word. -/
def componentEmpiricalWordLaw (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    Measure (Fin age → (Fin rule.edges × Bool)) :=
  (finiteWeightPMF (componentEmpiricalWordWeight rule marks fine age fallback)
    (componentEmpiricalWordWeight_nonnegative rule marks fine age fallback)
    (componentEmpiricalWordWeight_sum rule marks crossing fine age fallback)).toMeasure

instance componentEmpiricalWordLaw_probability (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    IsProbabilityMeasure (componentEmpiricalWordLaw rule marks crossing fine age fallback) := by
  unfold componentEmpiricalWordLaw
  infer_instance

theorem componentFrontierVertexMass_ratio_tendsto_zero (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (root_one : weight [] = 1)
    (convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (level_sum : ∀ age, ∑ word : Fin age → (Fin rule.edges × Bool), weight (List.ofFn word) = 1)
    (age : ℕ) :
    Tendsto (fun fine => componentFrontierVertexMass rule marks age [] /
      markedComponentVertexMass rule marks (fine + age) []) atTop (𝓝 0) := by
  have root_convergence := convergence []
  simp only [List.length_nil, Nat.add_zero, root_one] at root_convergence
  have root_positive : ∀ᶠ fine in atTop, 0 < markedComponentVertexMass rule marks (fine + age) [] := by
    have ratio_positive := (tendsto_order.mp (root_convergence.comp (tendsto_add_atTop_nat age))).1 0 zero_lt_one
    filter_upwards [ratio_positive] with fine positive
    exact (div_pos_iff.mp positive).elim (fun pair => pair.1) (fun pair =>
      False.elim (not_lt_of_ge (show 0 ≤ markedComponentVertexMass rule marks (fine + age) [] from Nat.cast_nonneg _) pair.1))
  have sum_convergence : Tendsto (fun fine => ∑ word : Fin age → (Fin rule.edges × Bool),
      markedComponentVertexMass rule marks fine (List.ofFn word) /
        markedComponentVertexMass rule marks (fine + age) []) atTop (𝓝 1) := by
    rw [← level_sum age]
    exact tendsto_finsetSum Finset.univ (fun (word : Fin age → (Fin rule.edges × Bool)) _ => by
      simpa only [List.length_ofFn] using convergence (List.ofFn word))
  have difference := (tendsto_const_nhds (x := (1 : ℝ))).sub sum_convergence
  simp only [sub_self] at difference
  apply difference.congr'
  filter_upwards [root_positive] with fine positive
  have partition := congrArg (fun count : ℝ => count / markedComponentVertexMass rule marks (fine + age) [])
    (actual_component_finite_partition rule marks crossing fine age [])
  simp only [List.nil_append, add_div, Finset.sum_div, div_self positive.ne'] at partition
  linarith

theorem componentEmpiricalWordWeight_tendsto (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (weight : List (Fin rule.edges × Bool) → ℝ) (root_one : weight [] = 1)
    (convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (level_sum : ∀ age, ∑ word : Fin age → (Fin rule.edges × Bool), weight (List.ofFn word) = 1)
    (age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool)) :
    Tendsto (fun fine => componentEmpiricalWordWeight rule marks fine age fallback word)
      atTop (𝓝 (weight (List.ofFn word))) := by
  have root_convergence := convergence []
  simp only [List.length_nil, Nat.add_zero, root_one] at root_convergence
  have root_positive : ∀ᶠ fine in atTop, 0 < markedComponentVertexMass rule marks (fine + age) [] := by
    have ratio_positive := (tendsto_order.mp (root_convergence.comp (tendsto_add_atTop_nat age))).1 0 zero_lt_one
    filter_upwards [ratio_positive] with fine positive
    exact (div_pos_iff.mp positive).elim (fun pair => pair.1) (fun pair =>
      False.elim (not_lt_of_ge (show 0 ≤ markedComponentVertexMass rule marks (fine + age) [] from Nat.cast_nonneg _) pair.1))
  have word_convergence : Tendsto (fun fine => markedComponentVertexMass rule marks fine (List.ofFn word) /
      markedComponentVertexMass rule marks (fine + age) []) atTop (𝓝 (weight (List.ofFn word))) := by
    simpa only [List.length_ofFn] using convergence (List.ofFn word)
  have frontier_convergence := componentFrontierVertexMass_ratio_tendsto_zero rule marks crossing weight root_one convergence level_sum age
  by_cases chosen : word = fallback
  · have total := word_convergence.add frontier_convergence
    simp only [add_zero] at total
    apply total.congr'
    filter_upwards [root_positive] with fine positive
    simp only [componentEmpiricalWordWeight, if_pos positive, if_pos chosen, add_div]
  · apply word_convergence.congr'
    filter_upwards [root_positive] with fine positive
    simp only [componentEmpiricalWordWeight, if_pos positive, if_neg chosen, add_zero]

/-- The actual finite counting laws, with any fixed allocation of their finite
birth frontier, converge to the same genuine component-cylinder weights. -/
theorem actual_component_empirical_probability_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
        (∀ address opened, rule.network.crosses (marks (address, opened)) = opened) ∧
        weight [] marks = 1 ∧
        (∀ address, 0 ≤ weight address marks ∧
          weight address marks = ∑ choice : Fin rule.edges × Bool, weight (address ++ [choice]) marks) ∧
        (∀ age, Tendsto (fun fine => componentFrontierVertexMass rule marks age [] /
          markedComponentVertexMass rule marks (fine + age) []) atTop (𝓝 0)) ∧
        ∀ age (fallback word : Fin age → (Fin rule.edges × Bool)),
          Tendsto (fun fine => componentEmpiricalWordWeight rule marks fine age fallback word)
            atTop (𝓝 (weight (List.ofFn word) marks)) := by
  obtain ⟨weight, properties⟩ := actual_component_cylinder_probability_weights classicalRule p positive below_one fixed_point
  refine ⟨weight, ?_⟩
  filter_upwards [properties, independentInnovationLaw_crosses rule p positive below_one fixed_point]
    with marks properties crossing
  have convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address marks)) := by
    intro address
    exact (properties.2.1 address).2.2.1
  refine ⟨crossing, properties.1, fun address => ⟨(properties.2.1 address).1, (properties.2.1 address).2.1⟩,
    fun age => componentFrontierVertexMass_ratio_tendsto_zero rule marks crossing
      (fun address => weight address marks) properties.1 convergence properties.2.2 age, ?_⟩
  intro age fallback word
  exact componentEmpiricalWordWeight_tendsto rule marks crossing (fun address => weight address marks)
    properties.1 convergence properties.2.2 age fallback word

end
end IGSIII.Chemical.Substitution
