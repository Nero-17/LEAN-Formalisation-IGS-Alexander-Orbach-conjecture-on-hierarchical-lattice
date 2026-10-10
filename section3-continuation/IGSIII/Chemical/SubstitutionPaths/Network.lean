import IGSIII.Chemical.SubstitutionPaths
import Universality.Graph.Rule

set_option autoImplicit false

/-!
# The min-plus identity on the numbered IGS II network

The glued graph and the finite network `FiniteNetwork.substitute` have the same
distance by the existing explicit graph isomorphism. This file transports the
proved path identity through that isomorphism.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

theorem iso_distance_eq {First Second : Type*}
    {firstGraph : SimpleGraph First} {secondGraph : SimpleGraph Second}
    (isomorphism : firstGraph ≃g secondGraph) {source target : First}
    (reachable : firstGraph.Reachable source target) :
    secondGraph.dist (isomorphism source) (isomorphism target) =
      firstGraph.dist source target := by
  apply le_antisymm
  · obtain ⟨walk, length⟩ := reachable.exists_walk_length_eq_dist
    have bound := SimpleGraph.dist_le (walk.map isomorphism.toHom)
    simpa [SimpleGraph.Walk.length_map, length] using bound
  · have mappedReachable := reachable.map isomorphism.toHom
    obtain ⟨walk, length⟩ := mappedReachable.exists_walk_length_eq_dist
    have bound := SimpleGraph.dist_le (walk.map isomorphism.symm.toHom)
    simpa [SimpleGraph.Walk.length_map, length] using bound

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges)
variable (inner : FiniteNetwork innerVertices innerEdges)

theorem substitute_crosses
    (configuration : Fin outerEdges → Configuration innerEdges) :
    (outer.substitute inner).crosses (substitutionConfigurationEquiv configuration) =
      outer.crosses (inner.coarseConfiguration configuration) := by
  apply Bool.eq_iff_iff.mpr
  rw [(outer.substitute inner).crosses_eq_true, outer.crosses_eq_true]
  change ((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).Reachable
    (Fintype.equivFin _ (Sum.inl outer.source)) (Fintype.equivFin _ (Sum.inl outer.target)) ↔ _
  rw [outer.substitute_reachable_iff inner configuration]
  exact outer.substitutedReachable_iff inner configuration outer.source outer.target

theorem substitute_distance_eq_substituted_distance
    (configuration : Fin outerEdges → Configuration innerEdges)
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable source target) :
    ((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).dist
        (Fintype.equivFin _ (Sum.inl source)) (Fintype.equivFin _ (Sum.inl target)) =
      (outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) :=
  iso_distance_eq (outer.substitutionGraphIso inner configuration)
    (outer.coarseReachable_lifts inner configuration reachable)

/-- Exact chemical min-plus formula on the actual numbered finite network. -/
theorem substitute_terminal_distance_eq_shortest
    (configuration : Fin outerEdges → Configuration innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable
      outer.source outer.target) :
    (((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).dist
        (outer.substitute inner).source (outer.substitute inner).target : ℝ) =
      (graphPathFamily (outer.openGraph (inner.coarseConfiguration configuration))
        outer.source outer.target reachable).shortest
          (fun edge => (childDistanceCost outer inner configuration edge : ℝ)) := by
  change (((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).dist
      (Fintype.equivFin _ (Sum.inl outer.source))
      (Fintype.equivFin _ (Sum.inl outer.target)) : ℝ) = _
  rw [substitute_distance_eq_substituted_distance outer inner configuration reachable]
  exact substituted_distance_eq_shortest outer inner configuration simple reachable

end IGSIII.Chemical.Substitution
