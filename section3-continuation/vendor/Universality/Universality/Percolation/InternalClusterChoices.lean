import Universality.Percolation.InternalClusterDecomposition

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def internalClusterFamily (R : FiniteNetwork vertices edges) (configuration : Configuration edges) :
    Finset (Finset (Fin vertices)) :=
  (R.clusterFamily configuration).filter fun cluster => R.source ∉ cluster ∧ R.target ∉ cluster

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def InternalClusterChoices (configuration : Fin outerEdges → Configuration innerEdges) :=
  Σ edge : Fin outerEdges, {cluster // cluster ∈ S.internalClusterFamily (configuration edge)}

instance (configuration : Fin outerEdges → Configuration innerEdges) :
    Fintype (S.InternalClusterChoices configuration) := by
  unfold InternalClusterChoices
  infer_instance

def internalClusterChoiceImage (configuration : Fin outerEdges → Configuration innerEdges)
    (choice : S.InternalClusterChoices configuration) : Finset (Fin (Fintype.card (R.SubstitutionVertex S))) :=
  choice.2.val.map (R.cellEmbedding S choice.1)

theorem internalClusterChoiceImage_injective (configuration : Fin outerEdges → Configuration innerEdges) :
    Function.Injective (R.internalClusterChoiceImage S configuration) := by
  classical
  rintro ⟨firstEdge, firstCluster, hfirst⟩ ⟨secondEdge, secondCluster, hsecond⟩ heq
  obtain ⟨hfirstFamily, hfirstSource, hfirstTarget⟩ := Finset.mem_filter.mp hfirst
  obtain ⟨hsecondFamily, hsecondSource, hsecondTarget⟩ := Finset.mem_filter.mp hsecond
  obtain ⟨inside, hinside⟩ := Finset.card_pos.mp (S.cluster_card_pos _ firstCluster hfirstFamily)
  have hmem : R.cellEmbedding S firstEdge inside ∈ secondCluster.map (R.cellEmbedding S secondEdge) := by
    change firstCluster.map (R.cellEmbedding S firstEdge) = secondCluster.map (R.cellEmbedding S secondEdge) at heq
    rw [← heq]
    exact Finset.mem_map.mpr ⟨inside, hinside, rfl⟩
  obtain ⟨other, hother, hsame⟩ := Finset.mem_map.mp hmem
  have hs : inside ≠ S.source := fun heq => hfirstSource (heq ▸ hinside)
  have ht : inside ≠ S.target := fun heq => hfirstTarget (heq ▸ hinside)
  have hcell : R.cellVertex S secondEdge other = Sum.inr (firstEdge, ⟨inside, hs, ht⟩) := by
    have h := (Fintype.equivFin (R.SubstitutionVertex S)).injective hsame
    change R.cellVertex S secondEdge other = R.cellVertex S firstEdge inside at h
    rw [h, R.cellVertex_eq_interior S firstEdge ⟨inside, hs, ht⟩]
  have hedge := ((R.cellVertex_eq_interior_iff S secondEdge firstEdge other ⟨inside, hs, ht⟩).mp hcell).1
  subst secondEdge
  have hclusters : firstCluster = secondCluster := by
    apply Finset.map_injective (R.cellEmbedding S firstEdge)
    exact heq
  subst secondCluster
  rfl

theorem internalClusterChoiceImage_mem (configuration : Fin outerEdges → Configuration innerEdges)
    (choice : S.InternalClusterChoices configuration) :
    R.internalClusterChoiceImage S configuration choice ∈
      (R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration) ∧
    Disjoint (R.internalClusterChoiceImage S configuration choice) (R.coarseVertices S) := by
  rcases choice with ⟨edge, cluster, hcluster⟩
  obtain ⟨hfamily, hsource, htarget⟩ := Finset.mem_filter.mp hcluster
  obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hfamily
  constructor
  · change (S.clusterVertices _ root).map (R.cellEmbedding S edge) ∈ _
    rw [← R.internal_cluster_embedding S configuration edge root hsource htarget]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · exact R.internal_cluster_embedding_disjoint_coarse S configuration edge root hsource htarget

theorem internalClusterChoiceImage_range (configuration : Fin outerEdges → Configuration innerEdges) :
    Finset.univ.image (R.internalClusterChoiceImage S configuration) =
      ((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
        fun cluster => Disjoint cluster (R.coarseVertices S) := by
  classical
  ext cluster
  constructor
  · rintro hcluster
    obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp hcluster
    exact Finset.mem_filter.mpr (R.internalClusterChoiceImage_mem S configuration choice)
  · intro hcluster
    obtain ⟨hfamily, hdisjoint⟩ := Finset.mem_filter.mp hcluster
    obtain ⟨edge, child, hchild, hsource, htarget, heq⟩ :=
      R.cluster_avoiding_coarse_is_internal_cell S configuration cluster hfamily hdisjoint
    exact Finset.mem_image.mpr ⟨⟨edge, child, Finset.mem_filter.mpr ⟨hchild, hsource, htarget⟩⟩,
      Finset.mem_univ _, heq.symm⟩

end
end Universality.FiniteNetwork
