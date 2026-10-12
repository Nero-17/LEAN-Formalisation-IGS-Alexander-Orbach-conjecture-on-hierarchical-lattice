import IGSIII.Chemical.SubstitutionPaths.BlockPaths

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
open Universality Universality.FiniteNetwork
open scoped BigOperators

/-- Pointwise chemical bounds for every crossing configuration of the actual
finite generation, with the root and children extracted from that configuration.
No representation, path bound, or probabilistic conclusion is assumed. -/
theorem actual_configuration_terminal_distance_bounds
    (rule : Rule) (classicalRule : rule.Classical) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true) :
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1) ≤
      (((rule.generation depth).network.openGraph configuration).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) ∧
    (((rule.generation depth).network.openGraph configuration).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) ≤
      (longestTerminalPath rule.network : ℝ) ^ (depth + 1) := by
  classical
  induction depth with
  | zero =>
    change (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ 1 ≤
      ((rule.network.openGraph configuration).dist rule.network.source rule.network.target : ℝ) ∧
      ((rule.network.openGraph configuration).dist rule.network.source rule.network.target : ℝ) ≤
        (longestTerminalPath rule.network : ℝ) ^ 1
    rw [← edgePathFamily_shortest_unit rule.network classicalRule.simple configuration]
    simp only [pow_one]
    constructor
    · apply PathFamily.shortest_one_lower
      intro path membership
      exact_mod_cast (edgePathFamily_card_bounds rule.network classicalRule.simple configuration crossing membership).1
    · apply PathFamily.shortest_one_upper
      intro path membership
      exact_mod_cast (edgePathFamily_card_bounds rule.network classicalRule.simple configuration crossing membership).2
  | succ depth inductionHypothesis =>
    have rootCrossing : rule.network.crosses (generationRootConfiguration rule depth configuration) = true :=
      (generation_root_crosses rule depth configuration).trans crossing
    rw [generation_distance_eq_cellMinPlus rule classicalRule.simple,
      cellMinPlus_eq_edgePathFamily_shortest rule.network (rule.generation depth).network classicalRule.simple]
    constructor
    · apply PathFamily.le_shortest
      intro path membership
      have cardinality : (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ (path.card : ℝ) := by
        exact_mod_cast (edgePathFamily_card_bounds rule.network classicalRule.simple
          (generationRootConfiguration rule depth configuration) rootCrossing membership).1
      calc
        _ = (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) *
            (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1) := by rw [pow_succ]; ring
        _ ≤ (path.card : ℝ) *
            (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1) := by
          exact mul_le_mul_of_nonneg_right cardinality (pow_nonneg (Nat.cast_nonneg _) _)
        _ = ∑ _edge ∈ path,
            (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1) := by simp
        _ ≤ PathFamily.pathCost path (fun edge =>
            (((rule.generation depth).network.openGraph (generationTopCells rule depth configuration edge)).dist
              (rule.generation depth).network.source (rule.generation depth).network.target : ℝ)) := by
          apply Finset.sum_le_sum
          intro edge member
          exact (inductionHypothesis (generationTopCells rule depth configuration edge)
            (edgePathFamily_used_edge rule.network classicalRule.simple
              (generationRootConfiguration rule depth configuration) membership member)).1
    · obtain ⟨path, membership⟩ := (edgePathFamily rule.network (generationRootConfiguration rule depth configuration)).nonempty
      have cardinality : (path.card : ℝ) ≤ (longestTerminalPath rule.network : ℝ) := by
        exact_mod_cast (edgePathFamily_card_bounds rule.network classicalRule.simple
          (generationRootConfiguration rule depth configuration) rootCrossing membership).2
      calc
        _ ≤ PathFamily.pathCost path (fun edge =>
            (((rule.generation depth).network.openGraph (generationTopCells rule depth configuration edge)).dist
              (rule.generation depth).network.source (rule.generation depth).network.target : ℝ)) :=
          PathFamily.shortest_le_pathCost _ _ membership
        _ ≤ ∑ _edge ∈ path, (longestTerminalPath rule.network : ℝ) ^ (depth + 1) := by
          apply Finset.sum_le_sum
          intro edge member
          exact (inductionHypothesis (generationTopCells rule depth configuration edge)
            (edgePathFamily_used_edge rule.network classicalRule.simple
              (generationRootConfiguration rule depth configuration) membership member)).2
        _ = (path.card : ℝ) * (longestTerminalPath rule.network : ℝ) ^ (depth + 1) := by simp
        _ ≤ (longestTerminalPath rule.network : ℝ) * (longestTerminalPath rule.network : ℝ) ^ (depth + 1) :=
          mul_le_mul_of_nonneg_right cardinality (pow_nonneg (Nat.cast_nonneg _) _)
        _ = _ := by rw [pow_succ]; ring

/-- The manuscript's generation-zero crossing seed has terminal distance one. -/
theorem actual_seed_terminal_distance_bounds (rule : Rule) :
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ 0 ≤ (1 : ℝ) ∧
      (1 : ℝ) ≤ (longestTerminalPath rule.network : ℝ) ^ 0 := by simp

end IGSIII.Chemical.Substitution
