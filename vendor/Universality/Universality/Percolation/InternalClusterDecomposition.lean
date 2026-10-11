import Universality.Percolation.CoarseClusterCounting

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem cellEmbedding_source_mem_coarse (edge : Fin outerEdges) :
    R.cellEmbedding S edge S.source ∈ R.coarseVertices S := by
  change Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.source) ∈ _
  rw [R.cellVertex_source]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem cellEmbedding_target_mem_coarse (edge : Fin outerEdges) :
    R.cellEmbedding S edge S.target ∈ R.coarseVertices S := by
  change Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.target) ∈ _
  rw [R.cellVertex_target]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem cell_reachable_lifts (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) {first second : Fin innerVertices}
    (h : (S.openGraph (configuration edge)).Reachable first second) :
    ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).Reachable
      (R.cellEmbedding S edge first) (R.cellEmbedding S edge second) :=
  (R.substitute_reachable_iff S configuration _ _).mpr (h.map (R.cellHom S configuration edge))

theorem cell_cluster_avoiding_coarse_avoids_terminals
    (configuration : Fin outerEdges → Configuration innerEdges) (edge : Fin outerEdges) (root : Fin innerVertices)
    (hdisjoint : Disjoint
      ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration) (R.cellEmbedding S edge root))
      (R.coarseVertices S)) :
    S.source ∉ S.clusterVertices (configuration edge) root ∧
      S.target ∉ S.clusterVertices (configuration edge) root := by
  constructor
  · intro hsource
    exact Finset.disjoint_left.mp hdisjoint
      ((R.substitute S).mem_clusterVertices _ _ _ |>.mpr
        (R.cell_reachable_lifts S configuration edge ((S.mem_clusterVertices _ _ _).mp hsource)))
      (R.cellEmbedding_source_mem_coarse S edge)
  · intro htarget
    exact Finset.disjoint_left.mp hdisjoint
      ((R.substitute S).mem_clusterVertices _ _ _ |>.mpr
        (R.cell_reachable_lifts S configuration edge ((S.mem_clusterVertices _ _ _).mp htarget)))
      (R.cellEmbedding_target_mem_coarse S edge)

/-- Every fine component avoiding the coarse skeleton is exactly one intact
internal component of one child cell. -/
theorem cluster_avoiding_coarse_is_internal_cell
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cluster : Finset (Fin (Fintype.card (R.SubstitutionVertex S))))
    (hcluster : cluster ∈ (R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration))
    (hdisjoint : Disjoint cluster (R.coarseVertices S)) :
    ∃ edge : Fin outerEdges, ∃ child : Finset (Fin innerVertices),
      child ∈ S.clusterFamily (configuration edge) ∧ S.source ∉ child ∧ S.target ∉ child ∧
        cluster = child.map (R.cellEmbedding S edge) := by
  obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hcluster
  obtain ⟨root, rfl⟩ := (Fintype.equivFin (R.SubstitutionVertex S)).surjective root
  cases root with
  | inl old =>
    exact (Finset.disjoint_left.mp hdisjoint
      ((R.substitute S).root_mem_clusterVertices _ _) (Finset.mem_image.mpr ⟨old, Finset.mem_univ _, rfl⟩)).elim
  | inr pair =>
    rcases pair with ⟨edge, inside⟩
    have heq : Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, inside)) =
        R.cellEmbedding S edge inside.val := by
      change _ = Fintype.equivFin _ (R.cellVertex S edge inside.val)
      rw [R.cellVertex_eq_interior]
    rw [heq] at hdisjoint ⊢
    obtain ⟨hsource, htarget⟩ := R.cell_cluster_avoiding_coarse_avoids_terminals S configuration edge inside.val hdisjoint
    refine ⟨edge, S.clusterVertices (configuration edge) inside.val,
      Finset.mem_image.mpr ⟨inside.val, Finset.mem_univ _, rfl⟩, hsource, htarget, ?_⟩
    exact R.internal_cluster_embedding S configuration edge inside.val hsource htarget

end
end Universality.FiniteNetwork
