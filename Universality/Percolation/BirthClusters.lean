import Universality.Percolation.ClusterNumberRecursion

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem internalClusterCount_eq_filter (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (size : ℕ) :
    R.internalClusterCount configuration size =
      ((R.internalClusterFamily configuration).filter fun cluster => cluster.card = size).card := by
  unfold internalClusterCount internalClusterFamily
  congr 1
  ext cluster
  simp only [Finset.mem_filter]
  tauto

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def birthClusterFamily (configuration : Fin outerEdges → Configuration innerEdges) :
    Finset (Finset (Fin (Fintype.card (R.SubstitutionVertex S)))) :=
  ((R.substitute S).internalClusterFamily (substitutionConfigurationEquiv configuration)).filter
    fun cluster => ¬ Disjoint cluster (R.coarseVertices S)

def birthClusterCount (configuration : Fin outerEdges → Configuration innerEdges) (size : ℕ) : ℕ :=
  ((R.birthClusterFamily S configuration).filter fun cluster => cluster.card = size).card

theorem clusters_avoiding_coarse_size_count (configuration : Fin outerEdges → Configuration innerEdges) (size : ℕ) :
    ((((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
      fun cluster => Disjoint cluster (R.coarseVertices S)).filter fun cluster => cluster.card = size).card =
      ∑ edge, S.internalClusterCount (configuration edge) size := by
  classical
  rw [← R.internalClusterChoiceImage_range S configuration, Finset.filter_image,
    Finset.card_image_of_injective _ (R.internalClusterChoiceImage_injective S configuration)]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ choice : S.InternalClusterChoices configuration,
    if (R.internalClusterChoiceImage S configuration choice).card = size then 1 else 0) = _
  simp only [internalClusterChoiceImage, Finset.card_map]
  change (∑ choice : (Σ edge : Fin outerEdges, {cluster // cluster ∈ S.internalClusterFamily (configuration edge)}),
    if choice.2.val.card = size then 1 else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro edge _
  rw [S.internalClusterCount_eq_filter]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_coe_sort (S.internalClusterFamily (configuration edge))
    (fun cluster => if cluster.card = size then (1 : ℕ) else 0)

/-- Exact size-by-size decomposition into internal clusters of child cells
and clusters born at an internal vertex of the top rule. -/
theorem internalClusterCount_substitute (configuration : Fin outerEdges → Configuration innerEdges) (size : ℕ) :
    (R.substitute S).internalClusterCount (substitutionConfigurationEquiv configuration) size =
      (∑ edge, S.internalClusterCount (configuration edge) size) + R.birthClusterCount S configuration size := by
  classical
  have hsource : (R.substitute S).source ∈ R.coarseVertices S :=
    Finset.mem_image.mpr ⟨R.source, Finset.mem_univ _, rfl⟩
  have htarget : (R.substitute S).target ∈ R.coarseVertices S :=
    Finset.mem_image.mpr ⟨R.target, Finset.mem_univ _, rfl⟩
  have havoiding : (((R.substitute S).internalClusterFamily (substitutionConfigurationEquiv configuration)).filter
      fun cluster => cluster.card = size ∧ Disjoint cluster (R.coarseVertices S)) =
      ((((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
        fun cluster => Disjoint cluster (R.coarseVertices S)).filter fun cluster => cluster.card = size) := by
    ext cluster
    simp only [internalClusterFamily, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hfamily, hs, ht⟩, hsize, hdisjoint⟩
      exact ⟨⟨hfamily, hdisjoint⟩, hsize⟩
    · rintro ⟨⟨hfamily, hdisjoint⟩, hsize⟩
      exact ⟨⟨hfamily, fun hs => Finset.disjoint_left.mp hdisjoint hs hsource,
        fun ht => Finset.disjoint_left.mp hdisjoint ht htarget⟩, hsize, hdisjoint⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := ((R.substitute S).internalClusterFamily (substitutionConfigurationEquiv configuration)).filter
      fun cluster => cluster.card = size)
    (p := fun cluster => Disjoint cluster (R.coarseVertices S))
  simp only [Finset.filter_filter] at hsplit
  rw [havoiding, R.clusters_avoiding_coarse_size_count S configuration size] at hsplit
  rw [(R.substitute S).internalClusterCount_eq_filter]
  rw [← hsplit]
  congr 1
  unfold birthClusterCount birthClusterFamily
  congr 1
  ext cluster
  simp only [Finset.mem_filter]
  tauto

theorem birthClusterCount_le_vertices (configuration : Fin outerEdges → Configuration innerEdges) (size : ℕ) :
    R.birthClusterCount S configuration size ≤ outerVertices := by
  have hsubset : R.birthClusterFamily S configuration ⊆ R.coarseTouchedClusters S configuration := by
    intro cluster hcluster
    obtain ⟨hinternal, htouch⟩ := Finset.mem_filter.mp hcluster
    obtain ⟨hfamily, hs, ht⟩ := Finset.mem_filter.mp hinternal
    rw [R.coarseTouchedClusters_eq]
    obtain ⟨vertex, hvertex, hcoarse⟩ := Finset.not_disjoint_iff.mp htouch
    exact Finset.mem_filter.mpr ⟨hfamily, vertex, hcoarse, hvertex⟩
  calc
    _ ≤ (R.birthClusterFamily S configuration).card := Finset.card_filter_le _ _
    _ ≤ (R.coarseTouchedClusters S configuration).card := Finset.card_le_card hsubset
    _ = (R.clusterFamily (S.coarseConfiguration configuration)).card := R.coarseTouchedClusters_card S configuration
    _ ≤ outerVertices := by
      exact (Finset.card_image_le).trans_eq (by simp)

end
end Universality.FiniteNetwork
