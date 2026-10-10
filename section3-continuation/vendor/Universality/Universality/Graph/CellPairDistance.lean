import Universality.Graph.CellIsometry
import Universality.Graph.CoarseDistance
import Universality.Graph.SubstitutionFullConnectivity
import Universality.Percolation.InternalClusterEmbedding

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Replacing points in two cells by their stored source endpoints changes
their distance by at most twice the child diameter. -/
theorem substituted_cell_pair_distance_bounds
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ diameter)
    (first second : Fin outerEdges) (u v : Fin innerVertices) :
    R.fullGraph.dist (R.endpoint first).1 (R.endpoint second).1 *
        S.fullGraph.dist S.source S.target ≤
      (R.substitute S).fullGraph.dist (R.cellEmbedding S first u) (R.cellEmbedding S second v) +
        2 * diameter ∧
    (R.substitute S).fullGraph.dist (R.cellEmbedding S first u) (R.cellEmbedding S second v) ≤
      R.fullGraph.dist (R.endpoint first).1 (R.endpoint second).1 *
        S.fullGraph.dist S.source S.target + 2 * diameter := by
  let firstAnchor := Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint first).1)
  let secondAnchor := Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint second).1)
  have hsource (edge : Fin outerEdges) : R.cellEmbedding S edge S.source =
      Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).1) := by
    change Fintype.equivFin _ (R.cellVertex S edge S.source) = _
    rw [R.cellVertex_source]
  have hfirst : (R.substitute S).fullGraph.dist (R.cellEmbedding S first u) firstAnchor ≤ diameter := by
    have heq := R.substitute_cell_distance S hinner first u S.source
    change (R.substitute S).fullGraph.dist (R.cellEmbedding S first u)
      (R.cellEmbedding S first S.source) = _ at heq
    rw [hsource] at heq
    exact heq.le.trans (hdiameter u S.source)
  have hsecond : (R.substitute S).fullGraph.dist (R.cellEmbedding S second v) secondAnchor ≤ diameter := by
    have heq := R.substitute_cell_distance S hinner second v S.source
    change (R.substitute S).fullGraph.dist (R.cellEmbedding S second v)
      (R.cellEmbedding S second S.source) = _ at heq
    rw [hsource] at heq
    exact heq.le.trans (hdiameter v S.source)
  have hcoarse : (R.substitute S).fullGraph.dist firstAnchor secondAnchor =
      R.fullGraph.dist (R.endpoint first).1 (R.endpoint second).1 *
        S.fullGraph.dist S.source S.target :=
    R.substitute_coarse_distance S _ _ ((houter _).symm.trans (houter _)) (hinner _)
  have hconnected (a b : Fin (Fintype.card (R.SubstitutionVertex S))) :
      (R.substitute S).fullGraph.Reachable a b :=
    ((R.substitute_all_vertices_connected S houter hinner a).symm).trans
      (R.substitute_all_vertices_connected S houter hinner b)
  have hupperFirst := (hconnected (R.cellEmbedding S first u) firstAnchor).dist_triangle_left
    (R.cellEmbedding S second v)
  have hupperSecond := (hconnected firstAnchor secondAnchor).dist_triangle_left (R.cellEmbedding S second v)
  have hlowerFirst := (hconnected firstAnchor (R.cellEmbedding S first u)).dist_triangle_left secondAnchor
  have hlowerSecond := (hconnected (R.cellEmbedding S first u) (R.cellEmbedding S second v)).dist_triangle_left secondAnchor
  rw [SimpleGraph.dist_comm (u := secondAnchor) (v := R.cellEmbedding S second v)] at hupperSecond
  rw [SimpleGraph.dist_comm (u := firstAnchor) (v := R.cellEmbedding S first u)] at hlowerFirst
  constructor <;> omega

end
end Universality.FiniteNetwork
