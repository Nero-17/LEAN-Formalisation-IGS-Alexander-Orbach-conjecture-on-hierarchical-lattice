import IGSIII.Chemical.SubstitutionPaths.Recursion

set_option autoImplicit false

/-!
# Noncrossing child components do not change old-vertex distances

This makes explicit why dangling components inside noncrossing cells can be
omitted from the deterministic terminal-distance recursion. Such cells need
not be empty in the original percolated graph.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges)
variable (inner : FiniteNetwork innerVertices innerEdges)

theorem substituted_distance_congr
    (first second : Fin outerEdges → Configuration innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (sameCrossing : ∀ edge, inner.crosses (first edge) = inner.crosses (second edge))
    (sameDistance : ∀ edge, inner.crosses (first edge) = true →
      (inner.openGraph (first edge)).dist inner.source inner.target =
        (inner.openGraph (second edge)).dist inner.source inner.target)
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration first)).Reachable source target) :
    (outer.substitutedGraph inner first).dist (Sum.inl source) (Sum.inl target) =
      (outer.substitutedGraph inner second).dist (Sum.inl source) (Sum.inl target) := by
  have coarse : inner.coarseConfiguration first = inner.coarseConfiguration second :=
    funext sameCrossing
  have secondReachable : (outer.openGraph (inner.coarseConfiguration second)).Reachable source target := by
    rwa [← coarse]
  have firstIdentity := substituted_distance_eq_shortest outer inner first simple reachable
  have secondIdentity := substituted_distance_eq_shortest_of_cost outer inner second
    (childDistanceCost outer inner first) (fun edge crossing => by
      rw [childDistanceCost_endpoint outer inner first simple edge]
      apply sameDistance edge
      rwa [sameCrossing edge]) secondReachable
  simp only [← coarse] at secondIdentity
  exact_mod_cast firstIdentity.trans secondIdentity.symm

noncomputable def eraseNoncrossingCells
    (configuration : Fin outerEdges → Configuration innerEdges) :
    Fin outerEdges → Configuration innerEdges :=
  fun edge => if inner.crosses (configuration edge) then configuration edge else fun _ => false

theorem eraseNoncrossingCells_crosses
    (configuration : Fin outerEdges → Configuration innerEdges) (edge : Fin outerEdges) :
    inner.crosses (eraseNoncrossingCells inner configuration edge) =
      inner.crosses (configuration edge) := by
  cases crossing : inner.crosses (configuration edge) with
  | false => simp only [eraseNoncrossingCells, crossing, Bool.false_eq_true, if_false,
      closed_not_crosses]
  | true => simp only [eraseNoncrossingCells, crossing, if_true]

/-- Delete every edge of every noncrossing cell. All reachable old-vertex
distances are unchanged, even if those cells originally contained dangling
components joined to either terminal. -/
theorem erase_noncrossing_cells_preserves_distance
    (configuration : Fin outerEdges → Configuration innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable source target) :
    (outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) =
      (outer.substitutedGraph inner (eraseNoncrossingCells inner configuration)).dist
        (Sum.inl source) (Sum.inl target) := by
  apply substituted_distance_congr outer inner configuration
    (eraseNoncrossingCells inner configuration) simple
    (fun edge => (eraseNoncrossingCells_crosses inner configuration edge).symm) _ reachable
  intro edge crossing
  simp only [eraseNoncrossingCells, crossing, if_true]

end IGSIII.Chemical.Substitution
