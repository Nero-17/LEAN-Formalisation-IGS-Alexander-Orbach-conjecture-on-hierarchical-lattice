import Universality.Graph.NetworkEquivalence
import Universality.Percolation.FiniteClusterDensity

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
set_option maxHeartbeats 0
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
variable (equivalence : R.NetworkEquivalence S)

theorem clusterVertices (configuration : Configuration eR) (root : Fin vR) :
    S.clusterVertices (equivalence.configuration configuration) (equivalence.vertex root) =
      (R.clusterVertices configuration root).map equivalence.vertex.toEmbedding := by
  ext vertex
  obtain ⟨vertex, rfl⟩ := equivalence.vertex.surjective vertex
  have hreach : (S.openGraph (equivalence.configuration configuration)).Reachable
      (equivalence.vertex root) (equivalence.vertex vertex) ↔ (R.openGraph configuration).Reachable root vertex :=
    (equivalence.openGraphIso configuration).reachable_iff
  rw [S.mem_clusterVertices, hreach, ← R.mem_clusterVertices]
  constructor
  · intro hvertex
    exact Finset.mem_map.mpr ⟨vertex, hvertex, rfl⟩
  · intro hvertex
    obtain ⟨other, hother, heq⟩ := Finset.mem_map.mp hvertex
    have heq' : other = vertex := equivalence.vertex.injective heq
    simpa only [heq'] using hother

theorem clusterFamily (configuration : Configuration eR) :
    S.clusterFamily (equivalence.configuration configuration) =
      (R.clusterFamily configuration).image (fun cluster => cluster.map equivalence.vertex.toEmbedding) := by
  ext cluster
  constructor
  · intro hcluster
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hcluster
    obtain ⟨root, rfl⟩ := equivalence.vertex.surjective root
    exact Finset.mem_image.mpr ⟨R.clusterVertices configuration root,
      Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩, (equivalence.clusterVertices configuration root).symm⟩
  · intro hcluster
    obtain ⟨cluster, hfamily, rfl⟩ := Finset.mem_image.mp hcluster
    change cluster ∈ Finset.univ.image (R.clusterVertices configuration) at hfamily
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hfamily
    rw [← equivalence.clusterVertices]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem source_mem_map (cluster : Finset (Fin vR)) :
    S.source ∈ cluster.map equivalence.vertex.toEmbedding ↔ R.source ∈ cluster := by
  rw [← equivalence.source]
  constructor
  · intro h
    obtain ⟨vertex, hvertex, heq⟩ := Finset.mem_map.mp h
    simpa only [equivalence.vertex.injective heq] using hvertex
  · intro h
    exact Finset.mem_map.mpr ⟨R.source, h, rfl⟩

theorem target_mem_map (cluster : Finset (Fin vR)) :
    S.target ∈ cluster.map equivalence.vertex.toEmbedding ↔ R.target ∈ cluster := by
  rw [← equivalence.target]
  constructor
  · intro h
    obtain ⟨vertex, hvertex, heq⟩ := Finset.mem_map.mp h
    simpa only [equivalence.vertex.injective heq] using hvertex
  · intro h
    exact Finset.mem_map.mpr ⟨R.target, h, rfl⟩

theorem internalClusterCount (configuration : Configuration eR) (size : ℕ) :
    S.internalClusterCount (equivalence.configuration configuration) size = R.internalClusterCount configuration size := by
  unfold FiniteNetwork.internalClusterCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [equivalence.clusterFamily, Finset.sum_image]
  · simp only [Finset.sum_map, equivalence.source_mem_map, equivalence.target_mem_map]
  · intro first _ second _ heq
    exact Finset.map_injective equivalence.vertex.toEmbedding heq

theorem clusterCount (configuration : Configuration eR) (size : ℕ) :
    S.clusterCount (equivalence.configuration configuration) size = R.clusterCount configuration size := by
  unfold FiniteNetwork.clusterCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [equivalence.clusterFamily, Finset.sum_image]
  · simp only [Finset.sum_map]
  · intro first _ second _ heq
    exact Finset.map_injective equivalence.vertex.toEmbedding heq

end
end Universality.FiniteNetwork.NetworkEquivalence
