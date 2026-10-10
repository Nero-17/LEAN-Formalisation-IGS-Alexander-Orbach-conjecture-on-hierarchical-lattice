import Universality.Percolation.ClosedCoarseRadius
import Universality.Graph.SubstitutionFullConnectivity

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- A single crossing main cell, with short terminal attachments in all
other cells, gives an upper radius bound for roots away from its ends. -/
theorem isolated_cell_cluster_distance_le
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (cells : Fin outerEdges → Configuration innerEdges) (main : Fin outerEdges)
    (hcoarse : S.coarseConfiguration cells = onlyOpen main)
    (bound attachment : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ bound)
    (hattachments : ∀ edge, edge ≠ main → ∀ vertex,
      ((S.openGraph (cells edge)).Reachable S.source vertex → S.fullGraph.dist S.source vertex ≤ attachment) ∧
      ((S.openGraph (cells edge)).Reachable S.target vertex → S.fullGraph.dist S.target vertex ≤ attachment))
    (root : Fin innerVertices) (hroot : (S.openGraph (cells main)).Reachable S.source root)
    (hsourceBound : S.fullGraph.dist root S.source + attachment ≤ bound)
    (htargetBound : S.fullGraph.dist root S.target + attachment ≤ bound)
    (vertex : Fin (Fintype.card (R.SubstitutionVertex S)))
    (hreach : ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
      (R.cellEmbedding S main root) vertex) :
    (R.substitute S).fullGraph.dist (R.cellEmbedding S main root) vertex ≤ bound := by
  have hconnected (u v : Fin (Fintype.card (R.SubstitutionVertex S))) :
      (R.substitute S).fullGraph.Reachable u v :=
    (R.substitute_all_vertices_connected S houter hinner u).symm.trans
      (R.substitute_all_vertices_connected S houter hinner v)
  have hsource (edge : Fin outerEdges) : R.cellEmbedding S edge S.source =
      Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).1) := by
    change Fintype.equivFin _ (R.cellVertex S edge S.source) = _
    rw [R.cellVertex_source]
  have htarget (edge : Fin outerEdges) : R.cellEmbedding S edge S.target =
      Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).2) := by
    change Fintype.equivFin _ (R.cellVertex S edge S.target) = _
    rw [R.cellVertex_target]
  have hcell (edge : Fin outerEdges) (u v : Fin innerVertices) :
      (R.substitute S).fullGraph.dist (R.cellEmbedding S edge u) (R.cellEmbedding S edge v) = S.fullGraph.dist u v :=
    R.substitute_cell_distance S hinner edge u v
  have hcoarseReach {old : Fin outerVertices}
      (h : (R.openGraph (S.coarseConfiguration cells)).Reachable (R.endpoint main).1 old) :
      old = (R.endpoint main).1 ∨ old = (R.endpoint main).2 := by
    rw [hcoarse, R.reachable_onlyOpen_iff] at h
    rcases h with h | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  have hmainReach : ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
      (R.cellEmbedding S main S.source) (R.cellEmbedding S main root) := by
    change ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
      (Fintype.equivFin _ (R.cellVertex S main S.source))
      (Fintype.equivFin _ (R.cellVertex S main root))
    rw [R.substitute_reachable_iff S]
    exact hroot.map (R.cellHom S cells main)
  have hfromMain := hmainReach.trans hreach
  rw [hsource] at hfromMain
  have hcoarseBound (old : Fin outerVertices)
      (hold : old = (R.endpoint main).1 ∨ old = (R.endpoint main).2) :
      (R.substitute S).fullGraph.dist (R.cellEmbedding S main root)
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl old)) ≤ bound := by
    rcases hold with rfl | rfl
    · rw [← hsource main, hcell]
      omega
    · rw [← htarget main, hcell]
      omega
  have hattachmentBound (edge : Fin outerEdges) (terminal point : Fin innerVertices)
      (old : Fin outerVertices)
      (hterminal : R.cellEmbedding S edge terminal =
        Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl old))
      (hold : old = (R.endpoint main).1 ∨ old = (R.endpoint main).2)
      (hnear : S.fullGraph.dist terminal point ≤ attachment) :
      (R.substitute S).fullGraph.dist (R.cellEmbedding S main root) (R.cellEmbedding S edge point) ≤ bound := by
    have htriangle := (hconnected (R.cellEmbedding S main root) (R.cellEmbedding S edge terminal)).dist_triangle_left
      (R.cellEmbedding S edge point)
    rw [hcell, hterminal] at htriangle
    rcases hold with rfl | rfl
    · rw [← hsource main, hcell] at htriangle
      omega
    · rw [← htarget main, hcell] at htriangle
      omega
  obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (R.SubstitutionVertex S)).surjective vertex
  rw [R.substitute_reachable_iff S, R.substitutedReachable_iff_active S] at hfromMain
  cases vertex with
  | inl old =>
      exact hcoarseBound old (hcoarseReach hfromMain)
  | inr pair =>
      rcases pair with ⟨edge, inside⟩
      have hinside : R.cellEmbedding S edge inside.val =
          Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, inside)) := by
        simp [cellEmbedding, cellVertex, inside.property.1, inside.property.2]
      rw [← hinside]
      by_cases hedge : edge = main
      · subst edge
        rw [hcell]
        exact hdiameter root inside.val
      · change ((R.openGraph (S.coarseConfiguration cells)).Reachable (R.endpoint main).1 (R.endpoint edge).1 ∧
            (S.openGraph (cells edge)).Reachable S.source inside.val) ∨
          ((R.openGraph (S.coarseConfiguration cells)).Reachable (R.endpoint main).1 (R.endpoint edge).2 ∧
            (S.openGraph (cells edge)).Reachable S.target inside.val) at hfromMain
        rcases hfromMain with ⟨hold, hnear⟩ | ⟨hold, hnear⟩
        · exact hattachmentBound edge S.source inside.val (R.endpoint edge).1 (hsource edge)
            (hcoarseReach hold) ((hattachments edge hedge inside.val).1 hnear)
        · exact hattachmentBound edge S.target inside.val (R.endpoint edge).2 (htarget edge)
            (hcoarseReach hold) ((hattachments edge hedge inside.val).2 hnear)

end
end Universality.FiniteNetwork

