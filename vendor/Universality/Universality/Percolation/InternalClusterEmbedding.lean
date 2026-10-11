import Universality.Graph.InternalCellConnectivity
import Universality.Percolation.FiniteClusterDensity

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def cellEmbedding (edge : Fin outerEdges) :
    Fin innerVertices ↪ Fin (Fintype.card (R.SubstitutionVertex S)) where
  toFun vertex := Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge vertex)
  inj' := (Fintype.equivFin (R.SubstitutionVertex S)).injective.comp (R.cellVertex_injective S edge)

def coarseVertices : Finset (Fin (Fintype.card (R.SubstitutionVertex S))) :=
  Finset.univ.image (fun vertex : Fin outerVertices => Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl vertex))

/-- The full component is preserved, including its cardinality, when its
child-cell component avoids both planting vertices. -/
theorem internal_cluster_embedding (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (root : Fin innerVertices)
    (hsource : S.source ∉ S.clusterVertices (configuration edge) root)
    (htarget : S.target ∉ S.clusterVertices (configuration edge) root) :
    (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
        (R.cellEmbedding S edge root) =
      (S.clusterVertices (configuration edge) root).map (R.cellEmbedding S edge) := by
  ext vertex
  obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (R.SubstitutionVertex S)).surjective vertex
  rw [FiniteNetwork.mem_clusterVertices]
  change ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).Reachable
    (Fintype.equivFin _ (R.cellVertex S edge root)) (Fintype.equivFin _ vertex) ↔ _
  rw [R.substitute_reachable_iff S, R.internal_cell_reachable_iff S configuration edge root
    (by simpa only [S.mem_clusterVertices] using hsource)
    (by simpa only [S.mem_clusterVertices] using htarget)]
  simp only [Finset.mem_map, S.mem_clusterVertices]
  constructor
  · rintro ⟨inside, hreach, heq⟩
    exact ⟨inside, hreach, congrArg (Fintype.equivFin (R.SubstitutionVertex S)) heq⟩
  · rintro ⟨inside, hreach, heq⟩
    exact ⟨inside, hreach, (Fintype.equivFin (R.SubstitutionVertex S)).injective heq⟩

theorem internal_cluster_embedding_disjoint_coarse (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (root : Fin innerVertices)
    (hsource : S.source ∉ S.clusterVertices (configuration edge) root)
    (htarget : S.target ∉ S.clusterVertices (configuration edge) root) :
    Disjoint ((S.clusterVertices (configuration edge) root).map (R.cellEmbedding S edge)) (R.coarseVertices S) := by
  apply Finset.disjoint_left.mpr
  intro vertex hvertex hcoarse
  obtain ⟨inside, hinside, rfl⟩ := Finset.mem_map.mp hvertex
  obtain ⟨old, _, heq⟩ := Finset.mem_image.mp hcoarse
  have hs : inside ≠ S.source := fun heq => hsource (heq ▸ hinside)
  have ht : inside ≠ S.target := fun heq => htarget (heq ▸ hinside)
  have hcell : R.cellEmbedding S edge inside =
      Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, ⟨inside, hs, ht⟩)) :=
    congrArg (Fintype.equivFin (R.SubstitutionVertex S)) (R.cellVertex_eq_interior S edge ⟨inside, hs, ht⟩)
  rw [hcell] at heq
  have hbad := (Fintype.equivFin (R.SubstitutionVertex S)).injective heq
  cases hbad

theorem internal_cluster_embedding_card (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (root : Fin innerVertices)
    (hsource : S.source ∉ S.clusterVertices (configuration edge) root)
    (htarget : S.target ∉ S.clusterVertices (configuration edge) root) :
    ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (R.cellEmbedding S edge root)).card = (S.clusterVertices (configuration edge) root).card := by
  rw [R.internal_cluster_embedding S configuration edge root hsource htarget, Finset.card_map]

end
end Universality.FiniteNetwork
