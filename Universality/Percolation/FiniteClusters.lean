import Universality.Percolation.FiniteNetwork
import Universality.Graph.FiniteVolume

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- The actual open component of a vertex, including the vertex itself. -/
def clusterVertices (configuration : Configuration edges) (root : Fin vertices) : Finset (Fin vertices) :=
  Finset.univ.filter fun vertex => (R.openGraph configuration).reachableDecide root vertex

theorem mem_clusterVertices (configuration : Configuration edges) (root vertex : Fin vertices) :
    vertex ∈ R.clusterVertices configuration root ↔ (R.openGraph configuration).Reachable root vertex := by
  simp [clusterVertices, SimpleGraph.reachableDecide_eq_true]

theorem root_mem_clusterVertices (configuration : Configuration edges) (root : Fin vertices) :
    root ∈ R.clusterVertices configuration root :=
  (R.mem_clusterVertices configuration root root).mpr (.refl root)

theorem clusterVertices_eq_iff (configuration : Configuration edges) (root vertex : Fin vertices) :
    R.clusterVertices configuration root = R.clusterVertices configuration vertex ↔
      (R.openGraph configuration).Reachable root vertex := by
  constructor
  · intro h
    apply (R.mem_clusterVertices configuration root vertex).mp
    rw [h]
    exact R.root_mem_clusterVertices configuration vertex
  · intro h
    ext other
    simp only [R.mem_clusterVertices]
    exact ⟨fun hr => h.symm.trans hr, fun hv => h.trans hv⟩

/-- Each open cluster is listed once, independently of the choice of root. -/
def clusterFamily (configuration : Configuration edges) : Finset (Finset (Fin vertices)) :=
  Finset.univ.image (R.clusterVertices configuration)

theorem clusterFamily_fiber (configuration : Configuration edges) (cluster : Finset (Fin vertices))
    (hcluster : cluster ∈ R.clusterFamily configuration) :
    (Finset.univ.filter fun root => R.clusterVertices configuration root = cluster) = cluster := by
  obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hcluster
  ext vertex
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    R.clusterVertices_eq_iff, R.mem_clusterVertices]
  exact ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

/-- The finite mass transport identity underlying uniform-vertex sampling. -/
theorem sum_roots_eq_sum_clusters (configuration : Configuration edges)
    (response : Finset (Fin vertices) → ℝ) :
    (∑ root, response (R.clusterVertices configuration root)) =
      ∑ cluster ∈ R.clusterFamily configuration, (cluster.card : ℝ) * response cluster := by
  classical
  have hsum := Finset.sum_fiberwise_of_maps_to'
    (g := R.clusterVertices configuration) (t := R.clusterFamily configuration)
    (fun root (_ : root ∈ (Finset.univ : Finset (Fin vertices))) =>
      Finset.mem_image.mpr ⟨root, Finset.mem_univ root, rfl⟩) response
  change (∑ cluster ∈ R.clusterFamily configuration,
      ∑ root ∈ Finset.univ with R.clusterVertices configuration root = cluster, response cluster) = _ at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro cluster hcluster
  rw [R.clusterFamily_fiber configuration cluster hcluster]
  simp only [Finset.sum_const, nsmul_eq_mul]

def clusterCount (configuration : Configuration edges) (size : ℕ) : ℕ :=
  ((R.clusterFamily configuration).filter fun cluster => cluster.card = size).card

theorem root_mass_count (configuration : Configuration edges) (size : ℕ) :
    (∑ root : Fin vertices, if (R.clusterVertices configuration root).card = size then (1 : ℝ) else 0) =
      (size : ℝ) * R.clusterCount configuration size := by
  rw [R.sum_roots_eq_sum_clusters configuration (fun cluster => if cluster.card = size then 1 else 0)]
  unfold clusterCount
  rw [← Finset.sum_boole]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cluster _
  split_ifs with h
  · simp [h]
  · simp

theorem sum_cluster_card (configuration : Configuration edges) :
    (∑ cluster ∈ R.clusterFamily configuration, (cluster.card : ℝ)) = vertices := by
  have h := R.sum_roots_eq_sum_clusters configuration (fun _ => 1)
  simpa using h.symm

def finiteClusterDensity (p : ℝ) (size : ℕ) : ℝ :=
  (∑ configuration, bernoulliWeight p configuration * R.clusterCount configuration size) / vertices

def uniformVertexClusterMassProbability (p : ℝ) (size : ℕ) : ℝ :=
  (∑ configuration, bernoulliWeight p configuration *
    ∑ root : Fin vertices, if (R.clusterVertices configuration root).card = size then (1 : ℝ) else 0) / vertices

/-- Exact finite-volume relation between cluster density and the mass law
seen from an independent uniform vertex. No infinite-volume limit is assumed. -/
theorem uniformVertexClusterMassProbability_eq (p : ℝ) (size : ℕ) :
    R.uniformVertexClusterMassProbability p size = (size : ℝ) * R.finiteClusterDensity p size := by
  simp only [uniformVertexClusterMassProbability, finiteClusterDensity, R.root_mass_count]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro configuration _
  ring

end
end Universality.FiniteNetwork
