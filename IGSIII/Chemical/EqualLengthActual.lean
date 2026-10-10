import IGSIII.Chemical.ChemicalOmega
import Universality.Examples.DiamondOpenGeodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory IGSIII.Probability
open scoped ENNReal

theorem open_distance_eq_of_equal_terminal_path_lengths
    {vertices edges : ℕ} (network : FiniteNetwork vertices edges) (length : ℕ)
    (equalLengths : ∀ walk : network.fullGraph.Walk network.source network.target,
      walk.IsPath → walk.length = length)
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    (network.openGraph configuration).dist network.source network.target = length := by
  obtain ⟨walk, simple, distance⟩ := ((network.crosses_eq_true configuration).mp crossing).exists_path_of_dist
  have fullSimple := simple.mapLe (openGraph_le_fullGraph network configuration)
  have lengthEquality := equalLengths (walk.mapLe (openGraph_le_fullGraph network configuration)) fullSimple
  simpa only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map, distance] using lengthEquality

theorem chemicalTransfer_unit_iterate_eq_pow_of_equal_paths
    (rule : Rule) (classical : rule.Classical) (length : ℕ)
    (equalLengths : ∀ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
      walk.IsPath → walk.length = length)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    ((chemicalTransfer rule)^[depth] (fun _ => 1)) (innovationTreeShift rule address marks) = (length : ℝ) ^ depth := by
  induction depth generalizing address with
  | zero => simp
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', chemicalTransfer]
    have childValues : (fun edge : Fin rule.edges =>
        ((chemicalTransfer rule)^[depth] (fun _ => 1))
          (innovationTreeShift rule [edge] (innovationTreeShift rule address marks))) =
        fun _ => (length : ℝ) ^ depth := by
      funext edge
      rw [innovationTreeShift_append]
      exact inductionHypothesis (address ++ [edge])
    rw [childValues]
    have rootConfiguration : innovationTreeShift rule address marks ([], true) = marks (address, true) := by
      simp only [innovationTreeShift, List.append_nil]
    rw [rootConfiguration]
    calc
      _ = (length : ℝ) ^ depth * (edgePathFamily rule.network (marks (address, true))).shortest (fun _ => 1) := by
        simpa only [mul_one] using (edgePathFamily rule.network (marks (address, true))).shortest_scale
          (fun _ => 1) (pow_nonneg (Nat.cast_nonneg length) depth)
      _ = (length : ℝ) ^ depth * length := by
        rw [edgePathFamily_shortest_unit rule.network classical.simple,
          open_distance_eq_of_equal_terminal_path_lengths rule.network length equalLengths _ (crossing address true)]
      _ = _ := (pow_succ _ _).symm

theorem actual_marked_distance_eq_pow_of_equal_paths
    (rule : Rule) (classical : rule.Classical) (length : ℕ)
    (equalLengths : ∀ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
      walk.IsPath → walk.length = length)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth address true)).dist
      (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) = (length : ℝ) ^ (depth + 1) := by
  rw [← chemicalTransfer_iterate_eq_actual rule classical.simple marks crossing depth address]
  exact chemicalTransfer_unit_iterate_eq_pow_of_equal_paths rule classical length equalLengths marks crossing (depth + 1) address

theorem diamond_actual_crossing_distance (depth : ℕ)
    (configuration : Configuration (diamondRule.generation depth).edges)
    (crossing : (diamondRule.generation depth).network.crosses configuration = true) :
    ((diamondRule.generation depth).network.openGraph configuration).dist
      (diamondRule.generation depth).network.source (diamondRule.generation depth).network.target = 2 ^ (depth + 1) := by
  obtain ⟨walk, length⟩ := diamond_generation_open_geodesic depth configuration crossing
  apply le_antisymm
  · exact (SimpleGraph.dist_le walk).trans_eq length
  · rw [← diamond_generation_terminal_distance depth]
    exact ((diamondRule.generation depth).network.crosses_eq_true configuration).mp crossing |>.dist_anti
      (openGraph_le_fullGraph _ _)

end IGSIII.Chemical.Substitution
