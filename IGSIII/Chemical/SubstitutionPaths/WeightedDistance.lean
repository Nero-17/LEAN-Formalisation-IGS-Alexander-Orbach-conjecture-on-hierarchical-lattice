import IGSIII.Chemical.SubstitutionPaths.Potential
import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false

/-!
# Nonnegative weighted distance from actual simple graph paths

The value on a disconnected pair is zero, and every theorem using it as a
terminal distance records reachability. Loop erasure gives comparison with any
walk. This makes weighted distance a concrete source of potentials, rather than
an assumed certificate of a graph distance formula.
-/

namespace IGSIII.Chemical.Substitution

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

omit [Fintype Vertex] in
theorem simplePath_cost {graph : SimpleGraph Vertex} {source target : Vertex}
    (walk : graph.Walk source target) (simple : walk.IsPath)
    (cost : Sym2 Vertex → ℝ) :
    PathFamily.pathCost walk.edges.toFinset cost = (walk.edges.map cost).sum :=
  List.sum_toFinset cost simple.isTrail.edges_nodup

noncomputable def weightedDistance (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (source target : Vertex) : ℝ := by
  classical
  exact if reachable : graph.Reachable source target then
    (graphPathFamily graph source target reachable).shortest cost else 0

theorem weightedDistance_of_reachable (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) {source target : Vertex}
    (reachable : graph.Reachable source target) :
    weightedDistance graph cost source target =
      (graphPathFamily graph source target reachable).shortest cost := by
  simp [weightedDistance, reachable]

theorem weightedDistance_nonneg (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (source target : Vertex) : 0 ≤ weightedDistance graph cost source target := by
  classical
  by_cases reachable : graph.Reachable source target
  · rw [weightedDistance_of_reachable graph cost reachable]
    exact PathFamily.shortest_nonneg _ nonnegative
  · simp [weightedDistance, reachable]

theorem exists_weighted_geodesic (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) {source target : Vertex}
    (reachable : graph.Reachable source target) :
    ∃ walk : graph.Walk source target, walk.IsPath ∧
      (walk.edges.map cost).sum = weightedDistance graph cost source target := by
  obtain ⟨edges, membership, minimal⟩ :=
    (graphPathFamily graph source target reachable).exists_minimizer cost
  obtain ⟨walk, simple, rfl⟩ :=
    (mem_graphPathFamily graph source target reachable edges).mp membership
  refine ⟨walk, simple, ?_⟩
  rw [weightedDistance_of_reachable graph cost reachable, minimal, simplePath_cost walk simple]

theorem weightedDistance_le_walkCost (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    {source target : Vertex} (walk : graph.Walk source target) :
    weightedDistance graph cost source target ≤ (walk.edges.map cost).sum := by
  classical
  have reachable : graph.Reachable source target := ⟨walk⟩
  rw [weightedDistance_of_reachable graph cost reachable]
  have membership : walk.bypass.edges.toFinset ∈
      (graphPathFamily graph source target reachable).paths :=
    (mem_graphPathFamily graph source target reachable _).mpr
      ⟨walk.bypass, walk.bypass_isPath, rfl⟩
  calc
    (graphPathFamily graph source target reachable).shortest cost ≤
        PathFamily.pathCost walk.bypass.edges.toFinset cost :=
      PathFamily.shortest_le_pathCost _ _ membership
    _ = (walk.bypass.edges.map cost).sum := simplePath_cost _ walk.bypass_isPath cost
    _ ≤ (walk.edges.map cost).sum := by
      apply (walk.edges_bypass_sublist_edges.map cost).sum_le_sum
      intro value membership
      obtain ⟨edge, _, rfl⟩ := List.mem_map.mp membership
      exact nonnegative edge

@[simp] theorem weightedDistance_self (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (source : Vertex) : weightedDistance graph cost source source = 0 := by
  apply le_antisymm
  · simpa using weightedDistance_le_walkCost graph cost nonnegative (.nil : graph.Walk source source)
  · exact weightedDistance_nonneg graph cost nonnegative source source

theorem weightedDistance_adj_le (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (root : Vertex) {first second : Vertex} (adjacent : graph.Adj first second) :
    weightedDistance graph cost root first ≤
      weightedDistance graph cost root second + cost s(first, second) := by
  classical
  by_cases reachable : graph.Reachable root second
  · obtain ⟨walk, _, minimal⟩ := exists_weighted_geodesic graph cost reachable
    have bound := weightedDistance_le_walkCost graph cost nonnegative
      (walk.append (.cons adjacent.symm .nil))
    simpa only [SimpleGraph.Walk.edges_append, List.map_append, List.sum_append,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, minimal, Sym2.eq_swap] using bound
  · have firstUnreachable : ¬ graph.Reachable root first := fun firstReachable =>
      reachable (firstReachable.trans adjacent.reachable)
    simp only [weightedDistance, dif_neg firstUnreachable, dif_neg reachable, zero_add]
    exact nonnegative _

theorem weightedDistance_adj_bound (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (root : Vertex) {first second : Vertex} (adjacent : graph.Adj first second) :
    |weightedDistance graph cost root first - weightedDistance graph cost root second| ≤
      cost s(first, second) := by
  have forward := weightedDistance_adj_le graph cost nonnegative root adjacent
  have backward := weightedDistance_adj_le graph cost nonnegative root adjacent.symm
  rw [Sym2.eq_swap] at backward
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end IGSIII.Chemical.Substitution
