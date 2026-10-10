import Universality.Percolation.ClusterRadius
import Universality.Percolation.SimpleConfigurations

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- When every child fails to cross, a component attached to an old
vertex stays within one child diameter of that vertex. -/
theorem allClosed_coarseRoot_distance_le_terminal_bound
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ)
    (cells : Fin outerEdges → Configuration innerEdges)
    (hterminalBound : ∀ edge vertex,
      ((S.openGraph (cells edge)).Reachable S.source vertex → S.fullGraph.dist S.source vertex ≤ diameter) ∧
      ((S.openGraph (cells edge)).Reachable S.target vertex → S.fullGraph.dist S.target vertex ≤ diameter))
    (hcoarse : S.coarseConfiguration cells = fun _ => false)
    (root : Fin outerVertices) (vertex : Fin (Fintype.card (R.SubstitutionVertex S)))
    (hreach : ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)) vertex) :
    (R.substitute S).fullGraph.dist
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)) vertex ≤ diameter := by
  obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (R.SubstitutionVertex S)).surjective vertex
  rw [R.substitute_reachable_iff S, R.substitutedReachable_iff_active S] at hreach
  cases vertex with
  | inl old =>
      change (R.openGraph (S.coarseConfiguration cells)).Reachable root old at hreach
      rw [hcoarse, R.openGraph_all_closed, SimpleGraph.reachable_bot] at hreach
      subst old
      simp
  | inr pair =>
      rcases pair with ⟨edge, inside⟩
      change ((R.openGraph (S.coarseConfiguration cells)).Reachable root (R.endpoint edge).1 ∧
          (S.openGraph (cells edge)).Reachable S.source inside.val) ∨
        ((R.openGraph (S.coarseConfiguration cells)).Reachable root (R.endpoint edge).2 ∧
          (S.openGraph (cells edge)).Reachable S.target inside.val) at hreach
      rw [hcoarse, R.openGraph_all_closed] at hreach
      simp only [SimpleGraph.reachable_bot] at hreach
      have hinside : R.cellEmbedding S edge inside.val =
          Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, inside)) := by
        simp [cellEmbedding, cellVertex, inside.property.1, inside.property.2]
      rcases hreach with ⟨hroot, hnear⟩ | ⟨hroot, hnear⟩
      · have hsource : R.cellEmbedding S edge S.source =
            Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root) := by
          change Fintype.equivFin _ (R.cellVertex S edge S.source) = _
          rw [R.cellVertex_source, hroot]
        have hdist := R.substitute_cell_distance S hinner edge S.source inside.val
        change (R.substitute S).fullGraph.dist (R.cellEmbedding S edge S.source)
          (R.cellEmbedding S edge inside.val) = S.fullGraph.dist S.source inside.val at hdist
        rw [hsource, hinside] at hdist
        exact hdist.le.trans ((hterminalBound edge inside.val).1 hnear)
      · have htarget : R.cellEmbedding S edge S.target =
            Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root) := by
          change Fintype.equivFin _ (R.cellVertex S edge S.target) = _
          rw [R.cellVertex_target, hroot]
        have hdist := R.substitute_cell_distance S hinner edge S.target inside.val
        change (R.substitute S).fullGraph.dist (R.cellEmbedding S edge S.target)
          (R.cellEmbedding S edge inside.val) = S.fullGraph.dist S.target inside.val at hdist
        rw [htarget, hinside] at hdist
        exact hdist.le.trans ((hterminalBound edge inside.val).2 hnear)

theorem allClosed_coarseRoot_distance_le
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ diameter)
    (cells : Fin outerEdges → Configuration innerEdges)
    (hcoarse : S.coarseConfiguration cells = fun _ => false)
    (root : Fin outerVertices) (vertex : Fin (Fintype.card (R.SubstitutionVertex S)))
    (hreach : ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)) vertex) :
    (R.substitute S).fullGraph.dist
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)) vertex ≤ diameter :=
  R.allClosed_coarseRoot_distance_le_terminal_bound S hinner diameter cells
    (fun _ vertex => ⟨fun _ => hdiameter S.source vertex, fun _ => hdiameter S.target vertex⟩)
    hcoarse root vertex hreach

end
end Universality.FiniteNetwork

