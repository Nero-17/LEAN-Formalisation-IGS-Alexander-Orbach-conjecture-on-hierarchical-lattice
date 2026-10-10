import IGSIII.Geometry.CellLocalisationCone
import Universality.Graph.ClassicalRule
import IGSIII.Chemical.SubstitutionPaths.Bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem weightedDistance_ge_edge_floor (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (floor : ℝ) (floor_nonnegative : 0 ≤ floor)
    (edge_floor : ∀ bond ∈ graph.edgeSet, floor ≤ cost bond)
    {first last : Vertex} (distinct : first ≠ last) (reachable : graph.Reachable first last) :
    floor ≤ weightedDistance graph cost first last := by
  classical
  let height (point : Vertex) : ℝ := if point = first then 0 else floor
  have bounded : ∀ {left right}, graph.Adj left right →
      |height left - height right| ≤ cost s(left, right) := by
    intro left right adjacent
    have bound := edge_floor s(left, right) adjacent
    dsimp only [height]
    split_ifs <;> simp only [sub_self, abs_zero, zero_sub, abs_neg,
      abs_of_nonneg floor_nonnegative, sub_zero]
    all_goals linarith
  have bound := weighted_potential_distance_bound graph cost height bounded reachable
  simpa only [height, if_pos rfl, if_neg distinct.symm, zero_sub, abs_neg,
    abs_of_nonneg floor_nonnegative] using bound

theorem weightedComponentBoundaryDistance_ge_edge_floor (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (floor : ℝ) (floor_nonnegative : 0 ≤ floor)
    (edge_floor : ∀ bond ∈ graph.edgeSet, floor ≤ cost bond)
    (source target point : Vertex) (not_source : point ≠ source) (not_target : point ≠ target)
    (anchored : graph.Reachable source point ∨ graph.Reachable target point) :
    floor ≤ weightedComponentBoundaryDistance graph cost source target point := by
  classical
  have source_bound (reachable : graph.Reachable source point) :
      floor ≤ weightedDistance graph cost source point :=
    weightedDistance_ge_edge_floor graph cost floor floor_nonnegative edge_floor not_source.symm reachable
  have target_bound (reachable : graph.Reachable target point) :
      floor ≤ weightedDistance graph cost target point :=
    weightedDistance_ge_edge_floor graph cost floor floor_nonnegative edge_floor not_target.symm reachable
  by_cases source_reached : graph.Reachable source point <;>
    by_cases target_reached : graph.Reachable target point
  · simpa only [weightedComponentBoundaryDistance, if_pos source_reached, if_pos target_reached] using
      le_min (source_bound source_reached) (target_bound target_reached)
  · simpa only [weightedComponentBoundaryDistance, if_pos source_reached, if_neg target_reached] using source_bound source_reached
  · simpa only [weightedComponentBoundaryDistance, if_neg source_reached, if_pos target_reached] using target_bound target_reached
  · exact False.elim (anchored.elim source_reached target_reached)

/-- Every crossing of a rule whose full terminal distance exceeds one contains
an actual retained nonterminal vertex. -/
theorem exists_retained_internal_vertex {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    ∃ point : Fin vertices, point ≠ network.source ∧ point ≠ network.target ∧
      (network.openGraph configuration).Reachable network.source point := by
  have reachable := (network.crosses_eq_true configuration).mp crossing
  obtain ⟨point, adjacent⟩ := reachable.nonempty_neighborSet_left network.terminals_distinct
  change (network.openGraph configuration).Adj network.source point at adjacent
  refine ⟨point, adjacent.ne.symm, ?_, adjacent.reachable⟩
  intro terminal
  subst point
  have full_adjacent : network.fullGraph.Adj network.source network.target :=
    openGraph_le_fullGraph network configuration adjacent
  have length_one := SimpleGraph.dist_eq_one_iff_adj.mpr full_adjacent
  omega
end
end IGSIII.Geometry



