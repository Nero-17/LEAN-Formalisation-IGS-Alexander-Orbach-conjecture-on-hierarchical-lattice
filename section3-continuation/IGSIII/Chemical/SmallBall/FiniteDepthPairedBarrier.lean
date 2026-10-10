import IGSIII.Chemical.SmallBall.PairedPathBarrier
import IGSIII.Chemical.SubstitutionPaths.BlockPaths
import IGSIII.Chemical.SubstitutionPaths.ChildHistoryLaw

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork Substitution
open scoped BigOperators

noncomputable section

variable {Outcome : Type*} [Fintype Outcome]

theorem actual_coarse_paired_child_barrier (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (coarse : ℕ) (childWeight : Bool → Outcome → ℝ) (first second : Outcome → ℝ)
    (weightNonnegative : ∀ opened outcome, 0 ≤ childWeight opened outcome)
    (normalized : ∀ opened, ∑ outcome, childWeight opened outcome = 1)
    {parameter scale ratio : ℝ} (parameterNonnegative : 0 ≤ parameter) (ratioNonnegative : 0 ≤ ratio)
    (pairedBound : (∑ outcome, childWeight true outcome * Real.exp (parameter * (first outcome - scale * second outcome))) ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) :
    (∑ configuration, (rule.generation coarse).network.conditionalCellWeight p true configuration *
      ∑ children : Fin (rule.generation coarse).edges → Outcome,
        if scale * (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => second (children edge)) <
          (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => first (children edge))
        then ∏ edge, childWeight (configuration edge) (children edge) else 0) ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (coarse + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
  have pointwise (configuration : Configuration (rule.generation coarse).edges)
      (crossing : (rule.generation coarse).network.crosses configuration = true) :
      (∑ children : Fin (rule.generation coarse).edges → Outcome,
        if scale * (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => second (children edge)) <
          (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => first (children edge))
        then ∏ edge, childWeight (configuration edge) (children edge) else 0) ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (coarse + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
    refine (finite_product_shortest_paired_barrier
      (edgePathFamily (rule.generation coarse).network configuration)
      (fun edge => childWeight (configuration edge)) (fun _ => first) (fun _ => second)
      (fun edge => weightNonnegative (configuration edge)) (fun edge => normalized (configuration edge))
      (ratio := ratio) parameterNonnegative (fun path membership edge edgeMembership => ?_)).trans ?_
    · rw [edgePathFamily_used_edge _ (classical.generation coarse).simple configuration membership edgeMembership]
      exact pairedBound
    · apply path_sum_le_geometric_tail_from_minimum _ _ _ ratioNonnegative (Nat.cast_nonneg _) _ geometricBelowOne
      · intro path membership
        rw [← rule.generation_terminal_distance (classical.connected _) coarse]
        exact (edgePathFamily_card_bounds _ (classical.generation coarse).simple configuration crossing membership).1
      · intro size
        exact_mod_cast actual_edgePathFamily_length_count rule classical coarse size configuration
  have averaged : (∑ configuration, (rule.generation coarse).network.conditionalCellWeight p true configuration *
      ∑ children : Fin (rule.generation coarse).edges → Outcome,
        if scale * (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => second (children edge)) <
          (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => first (children edge))
        then ∏ edge, childWeight (configuration edge) (children edge) else 0) ≤
      ∑ configuration, (rule.generation coarse).network.conditionalCellWeight p true configuration *
        (((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (coarse + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio)) := by
    apply Finset.sum_le_sum
    intro configuration _
    by_cases crossing : (rule.generation coarse).network.crosses configuration = true
    · exact mul_le_mul_of_nonneg_left (pointwise configuration crossing)
        ((rule.generation coarse).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    · simp [conditionalCellWeight, crossing]
  simpa only [← Finset.sum_mul, (rule.generation coarse).network.sum_conditionalCellWeight p
    (by rwa [rule.generation_fixed_point p fixedPoint]) (by rwa [rule.generation_fixed_point p fixedPoint]) true, one_mul] using averaged

theorem actual_generation_paired_child_barrier (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (coarse fine : ℕ) (first second : Configuration (rule.generation fine).edges → ℝ)
    {parameter scale ratio : ℝ} (parameterNonnegative : 0 ≤ parameter) (ratioNonnegative : 0 ≤ ratio)
    (pairedBound : (∑ configuration, (rule.generation fine).network.conditionalCellWeight p true configuration *
      Real.exp (parameter * (first configuration - scale * second configuration))) ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) :
    (∑ configuration, (rule.generation coarse).network.conditionalCellWeight p true configuration *
      ∑ children : Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges,
        if scale * (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => second (children edge)) <
          (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => first (children edge))
        then ∏ edge, (rule.generation fine).network.conditionalCellWeight p (configuration edge) (children edge) else 0) ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (coarse + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) :=
  actual_coarse_paired_child_barrier rule classical p positive lessOne fixedPoint coarse
    ((rule.generation fine).network.conditionalCellWeight p) first second
    ((rule.generation fine).network.conditionalCellWeight_nonneg positive.le lessOne.le)
    (fun opened => (rule.generation fine).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint]) (by rwa [rule.generation_fixed_point p fixedPoint]) opened)
    parameterNonnegative ratioNonnegative pairedBound geometricBelowOne

theorem actual_history_paired_child_barrier (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (coarse fine : ℕ) (first second : rule.ConfigurationHistory fine → ℝ)
    {parameter scale ratio : ℝ} (parameterNonnegative : 0 ≤ parameter) (ratioNonnegative : 0 ≤ ratio)
    (pairedBound : (∑ history, Rule.ConfigurationHistory.recursiveWeight rule p true fine history *
      Real.exp (parameter * (first history - scale * second history))) ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) :
    (∑ configuration, (rule.generation coarse).network.conditionalCellWeight p true configuration *
      ∑ children : Fin (rule.generation coarse).edges → rule.ConfigurationHistory fine,
        if scale * (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => second (children edge)) <
          (edgePathFamily (rule.generation coarse).network configuration).shortest
            (fun edge => first (children edge))
        then ∏ edge, Rule.ConfigurationHistory.recursiveWeight rule p (configuration edge) fine (children edge) else 0) ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
          (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (coarse + 1)) /
        (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) :=
  actual_coarse_paired_child_barrier rule classical p positive lessOne fixedPoint coarse
    (fun opened => Rule.ConfigurationHistory.recursiveWeight rule p opened fine) first second
    (fun opened => Rule.ConfigurationHistory.recursiveWeight_nonneg rule p positive lessOne fixedPoint opened fine)
    (fun opened => Rule.ConfigurationHistory.sum_recursiveWeight rule p positive lessOne fixedPoint opened fine)
    parameterNonnegative ratioNonnegative pairedBound geometricBelowOne

end
end IGSIII.Chemical.SmallBall
