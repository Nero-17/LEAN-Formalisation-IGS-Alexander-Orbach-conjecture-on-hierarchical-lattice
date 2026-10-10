import IGSIII.Chemical.SubstitutionPaths.ActualPathCounting
import IGSIII.Chemical.SubstitutionPaths.ConditionalLaw
import Universality.Graph.GeodesicEdgeLevels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

theorem edgePathFamily_shortest_unit {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) :
    (edgePathFamily network configuration).shortest (fun _ => 1) =
      ((network.openGraph configuration).dist network.source network.target : ℝ) := by
  classical
  by_cases reachable : (network.openGraph configuration).Reachable network.source network.target
  · rw [← graphPathFamily_shortest_unit _ _ _ reachable]
    apply le_antisymm
    · obtain ⟨path, membership, minimum⟩ :=
        (graphPathFamily (network.openGraph configuration) network.source network.target reachable).exists_minimizer (fun _ => 1)
      have indexedMembership : indexedPath network path ∈ (edgePathFamily network configuration).paths := by
        simp only [edgePathFamily, dif_pos reachable]
        exact Finset.mem_image.mpr ⟨path, membership, rfl⟩
      calc
        _ ≤ PathFamily.pathCost (indexedPath network path) (fun _ => 1) :=
          PathFamily.shortest_le_pathCost _ _ indexedMembership
        _ = PathFamily.pathCost path (fun _ => 1) :=
          indexedPath_cost network simple configuration reachable membership (fun _ : Sym2 (Fin vertices) => 1)
        _ = _ := minimum.symm
    · apply PathFamily.le_shortest
      intro path membership
      simp only [edgePathFamily, dif_pos reachable] at membership
      obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp membership
      rw [indexedPath_cost network simple configuration reachable bondMembership (fun _ => 1)]
      exact PathFamily.shortest_le_pathCost _ _ bondMembership
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable reachable]
    simp only [edgePathFamily, dif_neg reachable]
    obtain ⟨path, membership, minimum⟩ :=
      (PathFamily.exists_minimizer ({ paths := {∅}, nonempty := by simp } : PathFamily (Fin edges))
        (fun _ => 1))
    have empty : path = ∅ := by simpa using membership
    simpa [empty, PathFamily.pathCost] using minimum

theorem actual_edgePathFamily_length_count (rule : Rule) (classical : rule.Classical)
    (depth size : ℕ) (configuration : Configuration (rule.generation depth).edges) :
    (((edgePathFamily (rule.generation depth).network configuration).paths).filter
      (fun path => path.card = size)).card ≤ ((rule.edges + 3) ^ 4) ^ size := by
  classical
  have simple := (classical.generation depth).simple
  by_cases reachable : ((rule.generation depth).network.openGraph configuration).Reachable
      (rule.generation depth).network.source (rule.generation depth).network.target
  · apply (Finset.card_le_card_of_injOn
      (fun path => path.image (fun edge => s(((rule.generation depth).network.endpoint edge).1,
        ((rule.generation depth).network.endpoint edge).2))) ?_ ?_).trans
      (actual_open_simple_terminal_path_count rule classical depth size configuration)
    · intro path membership
      obtain ⟨pathMembership, sizeEquality⟩ := Finset.mem_filter.mp membership
      simp only [edgePathFamily, dif_pos reachable] at pathMembership
      obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp pathMembership
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [indexedPath_image _ configuration reachable bondMembership]
        exact bondMembership
      · rw [Finset.card_image_of_injective _ simple]
        exact sizeEquality
    · intro first _ second _ equality
      exact Finset.image_injective simple equality
  · simp only [edgePathFamily, dif_neg reachable]
    have bound : (Finset.filter (fun path : Finset (Fin (rule.generation depth).edges) => path.card = size) {∅}).card ≤ 1 :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_singleton _)
    exact bound.trans (one_le_pow₀ (one_le_pow₀ (by omega)))

theorem generation_block_conditioned_distance_observable (rule : Rule)
    (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ) (response : ℝ → ℝ) :
    (∑ configuration : Configuration (rule.generation (coarse + fine + 1)).edges,
      (rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true configuration *
        response (((rule.generation (coarse + fine + 1)).network.openGraph configuration).dist
          (rule.generation (coarse + fine + 1)).network.source
          (rule.generation (coarse + fine + 1)).network.target : ℝ)) =
      ∑ outerConfiguration : Configuration (rule.generation coarse).edges,
        (rule.generation coarse).network.conditionalCellWeight p true outerConfiguration *
          ∑ cells : Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges,
            (∏ edge, (rule.generation fine).network.conditionalCellWeight p (outerConfiguration edge) (cells edge)) *
              response (cellMinPlus (rule.generation coarse).network (rule.generation fine).network outerConfiguration cells) := by
  have law := conditional_substitution_distance_observable (rule.generation coarse).network
    (rule.generation fine).network (classical.generation coarse).simple p
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint]) response
  rw [← (rule.generationBlockDecomposition coarse fine).configuration.sum_comp] at law
  simpa only [NetworkEquivalence.conditionalCellWeight, networkEquivalence_terminal_distance_all,
    rule.generation_fixed_point p fixedPoint] using law

end IGSIII.Chemical.Substitution
