import IGSIII.Chemical.SubstitutionPaths.Network
import IGSIII.Mass.ShortestRouteBound

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open scoped BigOperators

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- The larger of the two actual terminal-component radii. In a noncrossing
configuration the two components are kept separate; unreachable distances are
zero. This dominates every retained terminal mask on the original configuration. -/
noncomputable def terminalComponentRadius (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : ℕ :=
  Finset.univ.sup (fun vertex => max
    ((network.openGraph configuration).dist network.source vertex)
    ((network.openGraph configuration).dist network.target vertex))

theorem source_distance_le_terminalComponentRadius (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (vertex : Fin vertices) :
    (network.openGraph configuration).dist network.source vertex ≤ terminalComponentRadius network configuration :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun vertex => max
    ((network.openGraph configuration).dist network.source vertex)
    ((network.openGraph configuration).dist network.target vertex)) (Finset.mem_univ vertex))

theorem target_distance_le_terminalComponentRadius (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (vertex : Fin vertices) :
    (network.openGraph configuration).dist network.target vertex ≤ terminalComponentRadius network configuration :=
  (le_max_right _ _).trans (Finset.le_sup (f := fun vertex => max
    ((network.openGraph configuration).dist network.source vertex)
    ((network.openGraph configuration).dist network.target vertex)) (Finset.mem_univ vertex))

theorem terminalComponentRadius_le (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (bound : ℕ)
    (source_bound : ∀ vertex, (network.openGraph configuration).dist network.source vertex ≤ bound)
    (target_bound : ∀ vertex, (network.openGraph configuration).dist network.target vertex ≤ bound) :
    terminalComponentRadius network configuration ≤ bound := by
  apply Finset.sup_le
  intro vertex _
  exact max_le (source_bound vertex) (target_bound vertex)

/-- Graph isomorphisms preserve distance also on unreachable pairs, where the
finite graph distance convention is zero on both sides. -/
theorem iso_distance_eq_all {First Second : Type*}
    {firstGraph : SimpleGraph First} {secondGraph : SimpleGraph Second}
    (isomorphism : firstGraph ≃g secondGraph) (source target : First) :
    secondGraph.dist (isomorphism source) (isomorphism target) = firstGraph.dist source target := by
  by_cases reachable : firstGraph.Reachable source target
  · exact iso_distance_eq isomorphism reachable
  · have mapped_unreachable : ¬ secondGraph.Reachable (isomorphism source) (isomorphism target) :=
      fun mapped => reachable (isomorphism.reachable_iff.mp mapped)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable reachable,
      SimpleGraph.dist_eq_zero_of_not_reachable mapped_unreachable]

theorem terminalComponentRadius_equivalence
    {otherVertices otherEdges : ℕ} {network : FiniteNetwork vertices edges}
    {other : FiniteNetwork otherVertices otherEdges}
    (equivalence : network.NetworkEquivalence other) (configuration : Configuration edges) :
    terminalComponentRadius other (equivalence.configuration configuration) = terminalComponentRadius network configuration := by
  have bound (vertex : Fin vertices) :
      max ((other.openGraph (equivalence.configuration configuration)).dist other.source (equivalence.vertex vertex))
        ((other.openGraph (equivalence.configuration configuration)).dist other.target (equivalence.vertex vertex)) =
      max ((network.openGraph configuration).dist network.source vertex)
        ((network.openGraph configuration).dist network.target vertex) := by
    rw [← equivalence.source, ← equivalence.target]
    exact congrArg₂ max (iso_distance_eq_all (equivalence.openGraphIso configuration) network.source vertex)
      (iso_distance_eq_all (equivalence.openGraphIso configuration) network.target vertex)
  apply le_antisymm
  · apply Finset.sup_le
    intro vertex _
    obtain ⟨previous, rfl⟩ := equivalence.vertex.surjective vertex
    rw [bound]
    exact Finset.le_sup (f := fun vertex => max
      ((network.openGraph configuration).dist network.source vertex)
      ((network.openGraph configuration).dist network.target vertex)) (Finset.mem_univ previous)
  · apply Finset.sup_le
    intro vertex _
    rw [← bound]
    exact Finset.le_sup (f := fun vertex => max
      ((other.openGraph (equivalence.configuration configuration)).dist other.source vertex)
      ((other.openGraph (equivalence.configuration configuration)).dist other.target vertex))
        (Finset.mem_univ (equivalence.vertex vertex))

theorem openGraph_distance_le_edges (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) {first last : Fin vertices}
    (reachable : (network.openGraph configuration).Reachable first last) :
    (network.openGraph configuration).dist first last ≤ edges := by
  obtain ⟨walk, simple, length⟩ := reachable.exists_path_of_dist
  calc
    _ = walk.length := length.symm
    _ ≤ (network.openGraph configuration).edgeFinset.card := simple.isTrail.length_le_card_edgeFinset
    _ ≤ openCount configuration := by
      rw [network.openGraph_edgeFinset]
      exact Finset.card_image_le
    _ ≤ edges := openCount_le configuration

variable (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)

/-- Each retained point has an available old-vertex anchor in its own actual
component, at distance at most the intrinsic radius of one child. -/
theorem retained_point_has_coarse_anchor
    (configuration : Fin outerEdges → Configuration innerEdges) (radius : ℕ)
    (radius_bound : ∀ edge, terminalComponentRadius inner (configuration edge) ≤ radius)
    (root : Fin outerVertices) (vertex : outer.SubstitutionVertex inner)
    (reachable : (outer.substitutedGraph inner configuration).Reachable (Sum.inl root) vertex) :
    ∃ anchor : Fin outerVertices,
      (outer.openGraph (inner.coarseConfiguration configuration)).Reachable root anchor ∧
      (outer.substitutedGraph inner configuration).dist (Sum.inl anchor) vertex ≤ radius := by
  rw [outer.substitutedReachable_iff_active inner configuration root vertex] at reachable
  cases vertex with
  | inl old => exact ⟨old, reachable, by simp⟩
  | inr pair =>
    rcases pair with ⟨edge, inside⟩
    change ((outer.openGraph (inner.coarseConfiguration configuration)).Reachable root (outer.endpoint edge).1 ∧
        (inner.openGraph (configuration edge)).Reachable inner.source inside.val) ∨
      ((outer.openGraph (inner.coarseConfiguration configuration)).Reachable root (outer.endpoint edge).2 ∧
        (inner.openGraph (configuration edge)).Reachable inner.target inside.val) at reachable
    have inside_identity : outer.cellVertex inner edge inside.val = Sum.inr (edge, inside) := by
      simp only [cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
      rfl
    rcases reachable with ⟨coarse_reachable, child_reachable⟩ | ⟨coarse_reachable, child_reachable⟩
    · obtain ⟨walk, length⟩ := child_reachable.exists_walk_length_eq_dist
      have distance_bound := SimpleGraph.dist_le (walk.map (outer.cellHom inner configuration edge))
      change (outer.substitutedGraph inner configuration).dist (outer.cellVertex inner edge inner.source)
        (outer.cellVertex inner edge inside.val) ≤ _ at distance_bound
      rw [outer.cellVertex_source, inside_identity, SimpleGraph.Walk.length_map, length] at distance_bound
      exact ⟨(outer.endpoint edge).1, coarse_reachable, distance_bound.trans
        ((source_distance_le_terminalComponentRadius inner _ _).trans (radius_bound edge))⟩
    · obtain ⟨walk, length⟩ := child_reachable.exists_walk_length_eq_dist
      have distance_bound := SimpleGraph.dist_le (walk.map (outer.cellHom inner configuration edge))
      change (outer.substitutedGraph inner configuration).dist (outer.cellVertex inner edge inner.target)
        (outer.cellVertex inner edge inside.val) ≤ _ at distance_bound
      rw [outer.cellVertex_target, inside_identity, SimpleGraph.Walk.length_map, length] at distance_bound
      exact ⟨(outer.endpoint edge).2, coarse_reachable, distance_bound.trans
        ((target_distance_le_terminalComponentRadius inner _ _).trans (radius_bound edge))⟩

/-- Actual one-step terminal radius control. Coarse paths use only crossing
children; all dangling branches are covered by the child radius term. -/
theorem substituted_terminal_radius_bound
    (configuration : Fin outerEdges → Configuration innerEdges) (radius terminal_bound : ℕ)
    (radius_bound : ∀ edge, terminalComponentRadius inner (configuration edge) ≤ radius)
    (crossing_bound : ∀ edge, inner.crosses (configuration edge) = true →
      (inner.openGraph (configuration edge)).dist inner.source inner.target ≤ terminal_bound)
    (root : Fin outerVertices) (vertex : outer.SubstitutionVertex inner)
    (reachable : (outer.substitutedGraph inner configuration).Reachable (Sum.inl root) vertex) :
    (outer.substitutedGraph inner configuration).dist (Sum.inl root) vertex ≤
      radius + outerEdges * terminal_bound := by
  obtain ⟨anchor, coarse_reachable, anchored⟩ := retained_point_has_coarse_anchor outer inner configuration
    radius radius_bound root vertex reachable
  have old_bound := substituted_distance_le_coarse_distance_mul outer inner configuration terminal_bound
    crossing_bound coarse_reachable
  have coarse_bound := openGraph_distance_le_edges outer _ coarse_reachable
  have old_reachable := outer.coarseReachable_lifts inner configuration coarse_reachable
  calc
    _ ≤ (outer.substitutedGraph inner configuration).dist (Sum.inl root) (Sum.inl anchor) +
        (outer.substitutedGraph inner configuration).dist (Sum.inl anchor) vertex :=
      old_reachable.dist_triangle_left vertex
    _ ≤ outerEdges * terminal_bound + radius :=
      Nat.add_le_add (old_bound.trans (Nat.mul_le_mul_right terminal_bound coarse_bound)) anchored
    _ = radius + outerEdges * terminal_bound := Nat.add_comm _ _

/-- The same bound holds on the actual numbered substitution network. -/
theorem terminalComponentRadius_substitute_le
    (configuration : Fin outerEdges → Configuration innerEdges) (radius terminal_bound : ℕ)
    (radius_bound : ∀ edge, terminalComponentRadius inner (configuration edge) ≤ radius)
    (crossing_bound : ∀ edge, inner.crosses (configuration edge) = true →
      (inner.openGraph (configuration edge)).dist inner.source inner.target ≤ terminal_bound) :
    terminalComponentRadius (outer.substitute inner) (substitutionConfigurationEquiv configuration) ≤
      radius + outerEdges * terminal_bound := by
  have rooted_bound (root : Fin outerVertices) (vertex : Fin (Fintype.card (outer.SubstitutionVertex inner))) :
      ((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).dist
        (Fintype.equivFin _ (Sum.inl root)) vertex ≤ radius + outerEdges * terminal_bound := by
    obtain ⟨point, rfl⟩ := (Fintype.equivFin (outer.SubstitutionVertex inner)).surjective vertex
    rw [show ((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).dist
        (Fintype.equivFin _ (Sum.inl root)) (Fintype.equivFin _ point) =
        (outer.substitutedGraph inner configuration).dist (Sum.inl root) point from
      iso_distance_eq_all (outer.substitutionGraphIso inner configuration) (Sum.inl root) point]
    by_cases reachable : (outer.substitutedGraph inner configuration).Reachable (Sum.inl root) point
    · exact substituted_terminal_radius_bound outer inner configuration radius terminal_bound radius_bound crossing_bound root point reachable
    · rw [SimpleGraph.dist_eq_zero_of_not_reachable reachable]
      exact Nat.zero_le _
  exact terminalComponentRadius_le _ _ _ (rooted_bound outer.source) (rooted_bound outer.target)

end IGSIII.Geometry
