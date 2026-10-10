import Universality.Graph.CrossingOpenCount
import Universality.Percolation.ClusterMass

set_option autoImplicit false

namespace Universality.FiniteNetwork

open scoped Classical

variable {vertices edges : ℕ}

private theorem long_walk_first_two {Vertex : Type*} {graph : SimpleGraph Vertex}
    {source target : Vertex} (walk : graph.Walk source target) (long_path : 1 < walk.length) :
    ∃ (middle next : Vertex) (adjacent : graph.Adj source middle)
      (next_adjacent : graph.Adj middle next) (rest : graph.Walk next target),
      walk = .cons adjacent (.cons next_adjacent rest) := by
  cases walk with
  | nil => simp at long_path
  | cons adjacent tail =>
    cases tail with
    | nil => simp at long_path
    | cons next_adjacent rest => exact ⟨_, _, adjacent, next_adjacent, rest, rfl⟩

/-- An open edge reached from the source is a connected child of the root
cluster, with its actual edge identifier retained. -/
theorem connected_child_of_reachable_adj (network : FiniteNetwork vertices edges)
    (coarse : Configuration edges) {first second : Fin vertices}
    (reachable : (network.openGraph coarse).Reachable network.source first)
    (adjacent : (network.openGraph coarse).Adj first second) :
    ∃ edge, network.childState .connected coarse edge = some .connected ∧
      s((network.endpoint edge).1, (network.endpoint edge).2) = s(first, second) := by
  obtain ⟨_, edge, opened, endpoints⟩ := adjacent
  refine ⟨edge, ?_, ?_⟩
  · apply (network.childState_connected_iff .connected coarse edge).mpr
    refine ⟨opened, ?_⟩
    simp only [active, show (LiveState.connected == LiveState.both) = false from rfl,
      Bool.false_and, Bool.or_false, SimpleGraph.reachableDecide_eq_true]
    rcases endpoints with forward | backward
    · rw [forward]
      exact reachable
    · rw [backward]
      exact reachable.trans (show (network.openGraph coarse).Adj first second from
        ⟨by simpa only [backward] using (network.loopless edge).symm,
          edge, opened, Or.inr backward⟩).reachable
  · rcases endpoints with forward | backward
    · simp only [forward]
    · simp only [backward]
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)

/-- Every crossing configuration has two distinct connected children when
the replacement network's terminal distance is at least two. -/
theorem crossing_has_two_connected_children (network : FiniteNetwork vertices edges)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (coarse : Configuration edges) (crossing : network.crosses coarse = true) :
    ∃ first second : Fin edges, first ≠ second ∧
      network.childState .connected coarse first = some .connected ∧
      network.childState .connected coarse second = some .connected := by
  have reachable := (network.crosses_eq_true coarse).mp crossing
  have subgraph : network.openGraph coarse ≤ network.fullGraph := by
    intro first second adjacent
    obtain ⟨different, edge, _, endpoints⟩ := adjacent
    exact ⟨different, edge, rfl, endpoints⟩
  obtain ⟨walk, simple, length⟩ := reachable.exists_path_of_dist
  have long_path : 1 < walk.length := by
    rw [length]
    exact scale.trans_le (reachable.dist_anti subgraph)
  obtain ⟨middle, next, adjacent, next_adjacent, rest, decomposition⟩ :=
    long_walk_first_two walk long_path
  obtain ⟨first_edge, first_connected, first_pair⟩ :=
    network.connected_child_of_reachable_adj coarse (.refl _) adjacent
  obtain ⟨second_edge, second_connected, second_pair⟩ :=
    network.connected_child_of_reachable_adj coarse adjacent.reachable next_adjacent
  refine ⟨first_edge, second_edge, ?_, first_connected, second_connected⟩
  intro equal_edges
  have equal_pairs : s(network.source, middle) = s(middle, next) := by
    rw [← first_pair, ← second_pair, equal_edges]
  have distinct_pairs := simple.isTrail.edges_nodup
  rw [decomposition] at distinct_pairs
  simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at distinct_pairs
  exact distinct_pairs.1 (by simp [equal_pairs])

end Universality.FiniteNetwork
