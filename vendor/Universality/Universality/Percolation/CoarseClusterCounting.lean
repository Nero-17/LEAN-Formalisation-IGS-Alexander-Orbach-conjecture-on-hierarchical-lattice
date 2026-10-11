import Universality.Percolation.InternalClusterEmbedding
import Universality.Graph.FiberCounting

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def coarseTouchedClusters (configuration : Fin outerEdges → Configuration innerEdges) :
    Finset (Finset (Fin (Fintype.card (R.SubstitutionVertex S)))) :=
  Finset.univ.image fun old : Fin outerVertices =>
    (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl old))

theorem coarseTouchedClusters_eq (configuration : Fin outerEdges → Configuration innerEdges) :
    R.coarseTouchedClusters S configuration =
      ((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
        fun cluster => ∃ vertex ∈ R.coarseVertices S, vertex ∈ cluster := by
  ext cluster
  constructor
  · rintro hcluster
    obtain ⟨old, _, rfl⟩ := Finset.mem_image.mp hcluster
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · exact ⟨_, Finset.mem_image.mpr ⟨old, Finset.mem_univ _, rfl⟩,
        (R.substitute S).root_mem_clusterVertices _ _⟩
  · intro hcluster
    obtain ⟨hfamily, vertex, hvertex, hmember⟩ := Finset.mem_filter.mp hcluster
    obtain ⟨old, _, rfl⟩ := Finset.mem_image.mp hvertex
    exact Finset.mem_image.mpr ⟨old, Finset.mem_univ _,
      (R.substitute S).clusterVertices_eq_of_mem _ cluster hfamily _ hmember⟩

/-- Fine clusters touching the old skeleton correspond exactly to coarse
open components, even if the child cells themselves contain internal clusters. -/
theorem coarseTouchedClusters_card (configuration : Fin outerEdges → Configuration innerEdges) :
    (R.coarseTouchedClusters S configuration).card =
      (R.clusterFamily (S.coarseConfiguration configuration)).card := by
  apply card_images_eq_of_fibers
  intro first _ second _
  rw [FiniteNetwork.clusterVertices_eq_iff, R.clusterVertices_eq_iff,
    R.substitute_reachable_iff S configuration, R.substitutedReachable_iff]

end
end Universality.FiniteNetwork
