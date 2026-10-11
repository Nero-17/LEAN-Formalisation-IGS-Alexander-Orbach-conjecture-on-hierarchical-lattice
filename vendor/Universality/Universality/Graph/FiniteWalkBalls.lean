import Universality.Graph.TowerDistance

namespace Universality
noncomputable section

def boundedWalkBall {Vertex : Type*} (graph : SimpleGraph Vertex) (root : Vertex)
    (radius : ℕ) : Set Vertex :=
  {vertex | ∃ walk : graph.Walk root vertex, walk.length ≤ radius}

theorem boundedWalkBall_finite {Vertex : Type*} (graph : SimpleGraph Vertex)
    (hfinite : ∀ vertex, (graph.neighborSet vertex).Finite) (root : Vertex) (radius : ℕ) :
    (boundedWalkBall graph root radius).Finite := by
  induction radius generalizing root with
  | zero =>
    apply (Set.finite_singleton root).subset
    rintro vertex ⟨walk, hlength⟩
    exact (walk.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hlength)).symm
  | succ radius ih =>
    have hneighbors : (⋃ vertex ∈ graph.neighborSet root,
        boundedWalkBall graph vertex radius).Finite :=
      (hfinite root).biUnion (fun vertex _ => ih vertex)
    apply ((Set.finite_singleton root).union hneighbors).subset
    rintro vertex ⟨walk, hlength⟩
    cases walk with
    | nil => exact Or.inl rfl
    | @cons first middle last adjacency rest =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨middle, Set.mem_iUnion.mpr ⟨adjacency, ?_⟩⟩)
      exact ⟨rest, by simpa only [SimpleGraph.Walk.length_cons, Nat.add_le_add_iff_right] using hlength⟩

theorem boundedWalkBall_eq_distBall {Vertex : Type*} (graph : SimpleGraph Vertex)
    (root : Vertex) (hconnected : ∀ vertex, graph.Reachable root vertex) (radius : ℕ) :
    boundedWalkBall graph root radius = {vertex | graph.dist root vertex ≤ radius} := by
  ext vertex
  constructor
  · rintro ⟨walk, hlength⟩
    exact (SimpleGraph.dist_le walk).trans hlength
  · intro hdistance
    change graph.dist root vertex ≤ radius at hdistance
    obtain ⟨walk, hlength⟩ := (hconnected vertex).exists_walk_length_eq_dist
    exact ⟨walk, by simpa only [hlength] using hdistance⟩

end
end Universality
