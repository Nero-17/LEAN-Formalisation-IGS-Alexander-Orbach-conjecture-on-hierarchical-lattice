import IGSIII.Chemical.PathFunctional
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

/-!
# Actual graph paths as a finite path family

The edge sets below come from simple terminal walks in a finite simple graph.
Thus the finite-family shortest-path functional is attached to an actual graph,
and unit edge costs recover its graph distance.  Reachability is explicit:
the empty family of paths in a disconnected graph is never assigned a minimum.
-/

namespace IGSIII.Chemical

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-- The edge sets of all actual simple walks between the two terminals. -/
noncomputable def graphPathSets (graph : SimpleGraph Vertex) (source target : Vertex) :
    Finset (Finset (Sym2 Vertex)) := by
  classical
  exact (Finset.univ : Finset (Sym2 Vertex)).powerset.filter fun edges =>
    ∃ walk : graph.Walk source target, walk.IsPath ∧ walk.edges.toFinset = edges

@[simp] theorem mem_graphPathSets (graph : SimpleGraph Vertex) (source target : Vertex)
    (edges : Finset (Sym2 Vertex)) :
    edges ∈ graphPathSets graph source target ↔
      ∃ walk : graph.Walk source target, walk.IsPath ∧ walk.edges.toFinset = edges := by
  classical
  simp [graphPathSets]

theorem graphPathSets_nonempty (graph : SimpleGraph Vertex) (source target : Vertex)
    (pathExists : ∃ walk : graph.Walk source target, walk.IsPath) :
    (graphPathSets graph source target).Nonempty := by
  obtain ⟨walk, simple⟩ := pathExists
  exact ⟨walk.edges.toFinset, (mem_graphPathSets graph source target _).mpr
    ⟨walk, simple, rfl⟩⟩

/-- Existence of a simple terminal path supplies the required nonempty family. -/
noncomputable def graphPathFamilyOfExistsPath (graph : SimpleGraph Vertex)
    (source target : Vertex)
    (pathExists : ∃ walk : graph.Walk source target, walk.IsPath) :
    PathFamily (Sym2 Vertex) where
  paths := graphPathSets graph source target
  nonempty := graphPathSets_nonempty graph source target pathExists

/-- The actual terminal path family of a graph with reachable terminals. -/
noncomputable def graphPathFamily (graph : SimpleGraph Vertex) (source target : Vertex)
    (reachable : graph.Reachable source target) : PathFamily (Sym2 Vertex) :=
  graphPathFamilyOfExistsPath graph source target (by
    obtain ⟨walk, simple, _⟩ := reachable.exists_path_of_dist
    exact ⟨walk, simple⟩)

@[simp] theorem mem_graphPathFamily (graph : SimpleGraph Vertex) (source target : Vertex)
    (reachable : graph.Reachable source target) (edges : Finset (Sym2 Vertex)) :
    edges ∈ (graphPathFamily graph source target reachable).paths ↔
      ∃ walk : graph.Walk source target, walk.IsPath ∧ walk.edges.toFinset = edges :=
  mem_graphPathSets graph source target edges

/- Simple paths have no repeated edges, so passing to a finite set preserves length. -/
omit [Fintype Vertex] in
theorem simplePath_edgeSet_card {graph : SimpleGraph Vertex} {source target : Vertex}
    (walk : graph.Walk source target) (simple : walk.IsPath) :
    walk.edges.toFinset.card = walk.length := by
  rw [List.toFinset_card_of_nodup simple.isTrail.edges_nodup, walk.length_edges]

theorem graphPathFamily_member_length (graph : SimpleGraph Vertex) (source target : Vertex)
    (reachable : graph.Reachable source target) {edges : Finset (Sym2 Vertex)}
    (membership : edges ∈ (graphPathFamily graph source target reachable).paths) :
    ∃ walk : graph.Walk source target,
      walk.IsPath ∧ walk.edges.toFinset = edges ∧ edges.card = walk.length := by
  obtain ⟨walk, simple, rfl⟩ :=
    (mem_graphPathFamily graph source target reachable edges).mp membership
  exact ⟨walk, simple, rfl, simplePath_edgeSet_card walk simple⟩

omit [Fintype Vertex] in
theorem simplePath_unit_cost {graph : SimpleGraph Vertex} {source target : Vertex}
    (walk : graph.Walk source target) (simple : walk.IsPath) :
    PathFamily.pathCost walk.edges.toFinset (fun _ => 1) = (walk.length : ℝ) := by
  have costCard : PathFamily.pathCost walk.edges.toFinset (fun _ => 1) =
      (walk.edges.toFinset.card : ℝ) := by
    simp [PathFamily.pathCost]
  rw [costCard, simplePath_edgeSet_card walk simple]

/-- Unit edge costs give the genuine graph distance, with no connectivity convention hidden. -/
theorem graphPathFamily_shortest_unit (graph : SimpleGraph Vertex) (source target : Vertex)
    (reachable : graph.Reachable source target) :
    (graphPathFamily graph source target reachable).shortest (fun _ => 1) =
      (graph.dist source target : ℝ) := by
  apply le_antisymm
  · obtain ⟨walk, simple, length⟩ := reachable.exists_path_of_dist
    have membership : walk.edges.toFinset ∈
        (graphPathFamily graph source target reachable).paths :=
      (mem_graphPathFamily graph source target reachable _).mpr ⟨walk, simple, rfl⟩
    calc
      (graphPathFamily graph source target reachable).shortest (fun _ => 1) ≤
          PathFamily.pathCost walk.edges.toFinset (fun _ => 1) :=
        PathFamily.shortest_le_pathCost _ _ membership
      _ = (graph.dist source target : ℝ) := by
        rw [simplePath_unit_cost walk simple, length]
  · apply PathFamily.le_shortest
    intro edges membership
    obtain ⟨walk, simple, rfl⟩ :=
      (mem_graphPathFamily graph source target reachable edges).mp membership
    rw [simplePath_unit_cost walk simple]
    exact_mod_cast graph.dist_le walk

end IGSIII.Chemical
