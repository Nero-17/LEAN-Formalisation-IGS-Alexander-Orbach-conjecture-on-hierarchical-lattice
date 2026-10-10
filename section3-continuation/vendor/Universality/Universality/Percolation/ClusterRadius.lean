import Universality.Percolation.BirthClusters
import Universality.Graph.CellIsometry
import Universality.Percolation.ClusterEquivalence

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Ambient graph radius about the specified root; different roots in the
same cluster can have different radii. -/
def clusterRadius (R : FiniteNetwork vertices edges) (cluster : Finset (Fin vertices))
    (root : Fin vertices) : ℕ := cluster.sup (R.fullGraph.dist root)

def rootClusterRadius (R : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (root : Fin vertices) : ℕ := R.clusterRadius (R.clusterVertices configuration root) root

def clusterRadiusRootCount (R : FiniteNetwork vertices edges) (cluster : Finset (Fin vertices))
    (radius : ℕ) : ℕ := (cluster.filter fun root => radius ≤ R.clusterRadius cluster root).card

def internalRadiusRootCount (R : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (radius : ℕ) : ℕ := ∑ cluster ∈ R.internalClusterFamily configuration,
      R.clusterRadiusRootCount cluster radius

def uniformVertexRadiusTailProbability (R : FiniteNetwork vertices edges) (p : ℝ) (radius : ℕ) : ℝ :=
  (∑ configuration, bernoulliWeight p configuration *
    ∑ root : Fin vertices, if radius ≤ R.rootClusterRadius configuration root then (1 : ℝ) else 0) / vertices

theorem sum_root_responses_eq_cluster_responses (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (response : Finset (Fin vertices) → Fin vertices → ℕ) :
    (∑ root, response (R.clusterVertices configuration root) root) =
      ∑ cluster ∈ R.clusterFamily configuration, ∑ root ∈ cluster, response cluster root := by
  classical
  have hsum := Finset.sum_fiberwise_of_maps_to
    (g := R.clusterVertices configuration) (t := R.clusterFamily configuration)
    (fun root (_ : root ∈ (Finset.univ : Finset (Fin vertices))) =>
      Finset.mem_image.mpr ⟨root, Finset.mem_univ root, rfl⟩)
    (fun root => response (R.clusterVertices configuration root) root)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro cluster hcluster
  rw [R.clusterFamily_fiber configuration cluster hcluster]
  apply Finset.sum_congr rfl
  intro root hroot
  rw [R.clusterVertices_eq_of_mem configuration cluster hcluster root hroot]

theorem root_radius_tail_count (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (radius : ℕ) :
    (∑ root : Fin vertices, if radius ≤ R.rootClusterRadius configuration root then (1 : ℕ) else 0) =
      ∑ cluster ∈ R.clusterFamily configuration, R.clusterRadiusRootCount cluster radius := by
  classical
  have h := R.sum_root_responses_eq_cluster_responses configuration
    (fun cluster root => if radius ≤ R.clusterRadius cluster root then 1 else 0)
  simpa only [rootClusterRadius, clusterRadiusRootCount, Finset.card_eq_sum_ones,
    Finset.sum_filter] using h

theorem clusterRadius_le_iff (R : FiniteNetwork vertices edges) (cluster : Finset (Fin vertices))
    (root : Fin vertices) (bound : ℕ) :
    R.clusterRadius cluster root ≤ bound ↔ ∀ vertex ∈ cluster, R.fullGraph.dist root vertex ≤ bound :=
  Finset.sup_le_iff

theorem dist_le_clusterRadius (R : FiniteNetwork vertices edges) (cluster : Finset (Fin vertices))
    (root vertex : Fin vertices) (hvertex : vertex ∈ cluster) :
    R.fullGraph.dist root vertex ≤ R.clusterRadius cluster root := Finset.le_sup hvertex

theorem clusterRadiusRootCount_le_card (R : FiniteNetwork vertices edges)
    (cluster : Finset (Fin vertices)) (radius : ℕ) : R.clusterRadiusRootCount cluster radius ≤ cluster.card :=
  Finset.card_filter_le _ _

theorem dist_le_twice_clusterRadius (R : FiniteNetwork vertices edges)
    (cluster : Finset (Fin vertices)) (root first second : Fin vertices)
    (hfirst : first ∈ cluster) (hsecond : second ∈ cluster)
    (hconnected : R.fullGraph.Reachable first root) :
    R.fullGraph.dist first second ≤ 2 * R.clusterRadius cluster root := by
  have ht := hconnected.dist_triangle_left second
  rw [show R.fullGraph.dist first root = R.fullGraph.dist root first from SimpleGraph.dist_comm] at ht
  have hboundFirst := R.dist_le_clusterRadius cluster root first hfirst
  have hboundSecond := R.dist_le_clusterRadius cluster root second hsecond
  omega

theorem clusterRadius_map (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (embedding : Fin innerVertices ↪ Fin outerVertices)
    (hdistance : ∀ u v, R.fullGraph.dist (embedding u) (embedding v) = S.fullGraph.dist u v)
    (cluster : Finset (Fin innerVertices)) (root : Fin innerVertices) :
    R.clusterRadius (cluster.map embedding) (embedding root) = S.clusterRadius cluster root := by
  unfold clusterRadius
  rw [Finset.sup_map]
  change cluster.sup (fun vertex => R.fullGraph.dist (embedding root) (embedding vertex)) =
    cluster.sup (S.fullGraph.dist root)
  congr 1
  funext vertex
  exact hdistance root vertex

theorem clusterRadiusRootCount_map (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (embedding : Fin innerVertices ↪ Fin outerVertices)
    (hdistance : ∀ u v, R.fullGraph.dist (embedding u) (embedding v) = S.fullGraph.dist u v)
    (cluster : Finset (Fin innerVertices)) (radius : ℕ) :
    R.clusterRadiusRootCount (cluster.map embedding) radius = S.clusterRadiusRootCount cluster radius := by
  unfold clusterRadiusRootCount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro root hroot
  change (radius ≤ R.clusterRadius (cluster.map embedding) (embedding root)) ↔ _
  rw [R.clusterRadius_map S embedding hdistance]

theorem substitute_cell_clusterRadius (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (edge : Fin outerEdges) (cluster : Finset (Fin innerVertices)) (root : Fin innerVertices) :
    (R.substitute S).clusterRadius (cluster.map (R.cellEmbedding S edge)) (R.cellEmbedding S edge root) =
      S.clusterRadius cluster root := by
  apply clusterRadius_map
  exact R.substitute_cell_distance S hinner edge

theorem substitute_cell_clusterRadiusRootCount (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (edge : Fin outerEdges) (cluster : Finset (Fin innerVertices)) (radius : ℕ) :
    (R.substitute S).clusterRadiusRootCount (cluster.map (R.cellEmbedding S edge)) radius =
      S.clusterRadiusRootCount cluster radius := by
  apply clusterRadiusRootCount_map
  exact R.substitute_cell_distance S hinner edge

theorem NetworkEquivalence.clusterRadius {R : FiniteNetwork outerVertices outerEdges}
    {S : FiniteNetwork innerVertices innerEdges} (equivalence : R.NetworkEquivalence S)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (cluster : Finset (Fin outerVertices)) (root : Fin outerVertices) :
    S.clusterRadius (cluster.map equivalence.vertex.toEmbedding) (equivalence.vertex root) =
      R.clusterRadius cluster root := by
  apply clusterRadius_map
  intro u v
  exact graph_iso_distance_of_reachable (equivalence.openGraphIso (fun _ => true)) ((hconnected u).symm.trans (hconnected v))

end
end Universality.FiniteNetwork
