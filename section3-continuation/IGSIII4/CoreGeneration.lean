import IGSIII4.CoreRelabel
import IGSIII4.CoreSubstitution
import Universality.Graph.ClassicalSubstitution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem terminalCoreEdges_card_eq_sum {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    ((terminalCoreEdges network configuration).card : ℝ) =
      ∑ edge, if edge ∈ terminalCoreEdges network configuration then (1 : ℝ) else 0 := by
  classical
  simp

theorem generation_terminalCore_member (rule : Rule) (classicalRule : rule.Classical) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (crossing : (rule.generation (depth + 1)).network.crosses configuration = true)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) :
    (rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)) ∈
      terminalCoreEdges (rule.generation (depth + 1)).network configuration ↔
    edge ∈ terminalCoreEdges rule.network (generationRootConfiguration rule depth configuration) ∧
      child ∈ terminalCoreEdges (rule.generation depth).network (generationTopCells rule depth configuration edge) := by
  have substituteSimple := substitute_simple (R := rule.network) (S := (rule.generation depth).network)
    (classicalRule.generation depth).simple (classicalRule.generation depth).scale
  have relabel := terminalCoreEdges_networkEquivalence_member (rule.generationTopDecomposition depth)
    (classicalRule.generation (depth + 1)).simple substituteSimple configuration crossing
    ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)))
  rw [Equiv.apply_symm_apply, ← configuration_of_topCells] at relabel
  rw [← relabel]
  exact terminalCoreEdges_substitution_member rule.network (rule.generation depth).network
    classicalRule.simple (classicalRule.generation depth).simple substituteSimple _
    ((generation_root_crosses rule depth configuration).trans crossing) edge child

theorem generation_terminalCore_card_recursion (rule : Rule) (classicalRule : rule.Classical) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (crossing : (rule.generation (depth + 1)).network.crosses configuration = true) :
    ((terminalCoreEdges (rule.generation (depth + 1)).network configuration).card : ℝ) =
      ∑ edge, if edge ∈ terminalCoreEdges rule.network (generationRootConfiguration rule depth configuration)
        then ((terminalCoreEdges (rule.generation depth).network (generationTopCells rule depth configuration edge)).card : ℝ)
        else 0 := by
  classical
  rw [terminalCoreEdges_card_eq_sum, ← (rule.generationTopDecomposition depth).edge.symm.sum_comp,
    ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp_rw [generation_terminalCore_member rule classicalRule depth configuration crossing]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases retained : edge ∈ terminalCoreEdges rule.network (generationRootConfiguration rule depth configuration)
  · simp only [retained, true_and, ite_true]
    exact (terminalCoreEdges_card_eq_sum _ _).symm
  · simp only [retained, false_and, ite_false, Finset.sum_const_zero]

end
end IGSIII4
