import Universality.Percolation.BirthRadiusRecursion
import Universality.Graph.ClassicalSubstitution

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
variable (equivalence : R.NetworkEquivalence S)

theorem clusterRadiusRootCount (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (cluster : Finset (Fin vR)) (radius : ℕ) :
    S.clusterRadiusRootCount (cluster.map equivalence.vertex.toEmbedding) radius =
      R.clusterRadiusRootCount cluster radius := by
  apply FiniteNetwork.clusterRadiusRootCount_map
  intro u v
  exact graph_iso_distance_of_reachable (equivalence.openGraphIso (fun _ => true))
    ((hconnected u).symm.trans (hconnected v))

theorem internalRadiusRootCount (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (configuration : Configuration eR) (radius : ℕ) :
    S.internalRadiusRootCount (equivalence.configuration configuration) radius =
      R.internalRadiusRootCount configuration radius := by
  unfold FiniteNetwork.internalRadiusRootCount FiniteNetwork.internalClusterFamily
  simp only [Finset.sum_filter]
  rw [equivalence.clusterFamily, Finset.sum_image]
  · simp only [equivalence.source_mem_map, equivalence.target_mem_map,
      equivalence.clusterRadiusRootCount hconnected]
  · intro first _ second _ heq
    exact Finset.map_injective equivalence.vertex.toEmbedding heq

include equivalence in
theorem expectedInternalRadiusRootCount
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex) (p : ℝ) (radius : ℕ) :
    S.expectedInternalRadiusRootCount p radius = R.expectedInternalRadiusRootCount p radius := by
  unfold FiniteNetwork.expectedInternalRadiusRootCount
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.bernoulliWeight, equivalence.internalRadiusRootCount hconnected]

end
end Universality.FiniteNetwork.NetworkEquivalence

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
open FiniteNetwork

theorem Classical.generation_expectedInternalRadiusRootCount {rule : Rule} (h : rule.Classical)
    (n : ℕ) (p : ℝ) (radius : ℕ) :
    (rule.generation (n + 1)).network.expectedInternalRadiusRootCount p radius =
      (rule.edges : ℝ) * (rule.generation n).network.expectedInternalRadiusRootCount p radius +
        rule.network.expectedBirthRadiusRootCount (rule.generation n).network p radius := by
  rw [← (rule.generationTopDecomposition n).expectedInternalRadiusRootCount (h.generation (n + 1)).connected,
    FiniteNetwork.expectedInternalRadiusRootCount_substitute _ _ (h.generation n).connected]

end
end Universality.Rule
