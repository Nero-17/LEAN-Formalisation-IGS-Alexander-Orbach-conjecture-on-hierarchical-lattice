import Universality.Percolation.IsolatedCellRadius
import Universality.Percolation.RadiusPointCounts
import Universality.Percolation.CoarseRootMass

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- An isolated internal cell transfers any family of roots with a
distance witness and controlled attachments into exact-radius root mass. -/
theorem internalRadiusPointRootCount_ge_isolated_cell
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (cells : Fin outerEdges → Configuration innerEdges) (main : Fin outerEdges)
    (hcoarse : S.coarseConfiguration cells = onlyOpen main)
    (hfirstSource : (R.endpoint main).1 ≠ R.source)
    (hfirstTarget : (R.endpoint main).1 ≠ R.target)
    (hsecondSource : (R.endpoint main).2 ≠ R.source)
    (hsecondTarget : (R.endpoint main).2 ≠ R.target)
    (bound attachment : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ bound)
    (hattachments : ∀ edge, edge ≠ main → ∀ vertex,
      ((S.openGraph (cells edge)).Reachable S.source vertex → S.fullGraph.dist S.source vertex ≤ attachment) ∧
      ((S.openGraph (cells edge)).Reachable S.target vertex → S.fullGraph.dist S.target vertex ≤ attachment))
    (selected : Finset (Fin innerVertices))
    (hselected : ∀ root ∈ selected, (S.openGraph (cells main)).Reachable S.source root ∧
      S.fullGraph.dist root S.source + attachment ≤ bound ∧
      S.fullGraph.dist root S.target + attachment ≤ bound)
    (hwitness : ∀ root ∈ selected, ∃ vertex,
      (S.openGraph (cells main)).Reachable S.source vertex ∧ S.fullGraph.dist root vertex = bound) :
    selected.card ≤ (R.substitute S).internalRadiusPointRootCount (substitutionConfigurationEquiv cells) bound := by
  classical
  let planted := Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint main).1)
  let cluster := (R.substitute S).clusterVertices (substitutionConfigurationEquiv cells) planted
  have hsource : R.cellEmbedding S main S.source = planted := by
    change Fintype.equivFin _ (R.cellVertex S main S.source) = _
    rw [R.cellVertex_source]
  have hclusterBirth : cluster ∈ R.birthClusterFamily S cells := by
    apply (R.coarseRoot_cluster_mem_birth_iff S cells (R.endpoint main).1).mpr
    rw [hcoarse]
    simp only [mem_clusterVertices, R.reachable_onlyOpen_iff]
    simp [hfirstSource, hfirstTarget, hsecondSource, hsecondTarget]
  have hclusterInternal : cluster ∈ (R.substitute S).internalClusterFamily (substitutionConfigurationEquiv cells) :=
    (Finset.mem_filter.mp hclusterBirth).1
  have hlift (vertex : Fin innerVertices) (hvertex : (S.openGraph (cells main)).Reachable S.source vertex) :
      ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable planted
        (R.cellEmbedding S main vertex) := by
    rw [← hsource]
    change ((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
      (Fintype.equivFin _ (R.cellVertex S main S.source))
      (Fintype.equivFin _ (R.cellVertex S main vertex))
    rw [R.substitute_reachable_iff S]
    exact hvertex.map (R.cellHom S cells main)
  have hsubset : selected.map (R.cellEmbedding S main) ⊆
      cluster.filter (fun root => (R.substitute S).clusterRadius cluster root = bound) := by
    intro root hroot
    obtain ⟨root, hselectedMember, rfl⟩ := Finset.mem_map.mp hroot
    obtain ⟨hconnected, hsourceBound, htargetBound⟩ := hselected root hselectedMember
    have hrootReach := hlift root hconnected
    have hrootMember : R.cellEmbedding S main root ∈ cluster :=
      ((R.substitute S).mem_clusterVertices _ _ _).mpr hrootReach
    refine Finset.mem_filter.mpr ⟨hrootMember, Nat.le_antisymm ?_ ?_⟩
    · apply ((R.substitute S).clusterRadius_le_iff cluster (R.cellEmbedding S main root) bound).mpr
      intro vertex hvertex
      have hvertexReach := ((R.substitute S).mem_clusterVertices _ _ _).mp hvertex
      exact R.isolated_cell_cluster_distance_le S houter hinner cells main hcoarse bound attachment
        hdiameter hattachments root hconnected hsourceBound htargetBound vertex
        (hrootReach.symm.trans hvertexReach)
    · obtain ⟨vertex, hvertexReach, hdistance⟩ := hwitness root hselectedMember
      have hvertexMember : R.cellEmbedding S main vertex ∈ cluster :=
        ((R.substitute S).mem_clusterVertices _ _ _).mpr (hlift vertex hvertexReach)
      have hlower := (R.substitute S).dist_le_clusterRadius cluster (R.cellEmbedding S main root)
        (R.cellEmbedding S main vertex) hvertexMember
      have hcell := R.substitute_cell_distance S hinner main root vertex
      change (R.substitute S).fullGraph.dist (R.cellEmbedding S main root)
        (R.cellEmbedding S main vertex) = S.fullGraph.dist root vertex at hcell
      rw [hcell, hdistance] at hlower
      exact hlower
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_map] at hcard
  change selected.card ≤ (R.substitute S).clusterRadiusPointRootCount cluster bound at hcard
  apply hcard.trans
  exact Finset.single_le_sum (f := fun component => (R.substitute S).clusterRadiusPointRootCount component bound)
    (fun _ _ => Nat.zero_le _) hclusterInternal

end
end Universality.FiniteNetwork


