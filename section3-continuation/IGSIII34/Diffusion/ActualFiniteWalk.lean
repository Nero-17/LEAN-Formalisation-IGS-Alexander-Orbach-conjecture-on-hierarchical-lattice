import IGSIII34.Diffusion.ActualDegreeRewards
import IGSIII34.Diffusion.ReversibleWalk
import IGSIII34.Diffusion.DegreeTransport

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open scoped BigOperators

variable {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
  (configuration : Configuration edges)

instance retainedVertexDecidableEq : DecidableEq (RetainedSkeletonVertex network configuration) :=
  Classical.decEq _

instance retainedVertexFintype : Fintype (RetainedSkeletonVertex network configuration) :=
  Fintype.ofFinite _

theorem clusterEdge_first_reachable (edge : ClusterEdge network configuration) :
    (network.openGraph configuration).Reachable network.source (network.endpoint edge.val).1 := by
  apply (network.openGraph configuration).reachableDecide_eq_true _ _ |>.mp
  simpa [FiniteNetwork.active] using edge.property.2

theorem clusterEdge_last_reachable (edge : ClusterEdge network configuration) :
    (network.openGraph configuration).Reachable network.source (network.endpoint edge.val).2 := by
  apply (clusterEdge_first_reachable network configuration edge).trans
  apply SimpleGraph.Adj.reachable
  exact ⟨network.loopless edge.val, edge.val, edge.property.1, Or.inl rfl⟩

def clusterRetainedEndpoint : ClusterEdge network configuration →
    RetainedSkeletonVertex network configuration × RetainedSkeletonVertex network configuration :=
  fun edge => (⟨(network.endpoint edge.val).1, clusterEdge_first_reachable network configuration edge⟩,
    ⟨(network.endpoint edge.val).2, clusterEdge_last_reachable network configuration edge⟩)

theorem retained_degree_eq (vertex : RetainedSkeletonVertex network configuration) :
    degree (clusterRetainedEndpoint network configuration) vertex =
      degree (clusterEndpoint network configuration) vertex.val := by
  classical
  unfold degree
  apply Finset.sum_congr rfl
  intro edge _
  have first : (clusterRetainedEndpoint network configuration edge).1 = vertex ↔
      (clusterEndpoint network configuration edge).1 = vertex.val :=
    ⟨fun equality => congrArg Subtype.val equality, fun equality => Subtype.ext equality⟩
  have last : (clusterRetainedEndpoint network configuration edge).2 = vertex ↔
      (clusterEndpoint network configuration edge).2 = vertex.val :=
    ⟨fun equality => congrArg Subtype.val equality, fun equality => Subtype.ext equality⟩
  simp only [first, last]

theorem cluster_degree_positive (crossing : network.crosses configuration = true)
    (vertex : RetainedSkeletonVertex network configuration) :
    0 < degree (clusterRetainedEndpoint network configuration) vertex := by
  classical
  rw [retained_degree_eq]
  have neighbor : (network.openGraph configuration).neighborSet vertex.val |>.Nonempty := by
    by_cases source : vertex.val = network.source
    · rw [source]
      exact ((network.crosses_eq_true configuration).mp crossing).nonempty_neighborSet_left network.terminals_distinct
    · exact vertex.property.symm.nonempty_neighborSet_left source
  obtain ⟨last, adjacent⟩ := neighbor
  obtain ⟨distinct, edge, opened, direction⟩ := adjacent
  have firstReachable : (network.openGraph configuration).Reachable network.source (network.endpoint edge).1 := by
    rcases direction with forward | backward
    · rw [forward]
      exact vertex.property
    · rw [backward]
      exact vertex.property.trans (SimpleGraph.Adj.reachable ⟨distinct, edge, opened, Or.inr backward⟩)
  let retainedEdge : ClusterEdge network configuration := ⟨edge, opened, by
    simpa [FiniteNetwork.active] using
      ((network.openGraph configuration).reachableDecide_eq_true network.source (network.endpoint edge).1).mpr firstReachable⟩
  have termPositive : 0 < ((if (clusterEndpoint network configuration retainedEdge).1 = vertex.val then (1 : ℝ) else 0) +
      (if (clusterEndpoint network configuration retainedEdge).2 = vertex.val then 1 else 0)) := by
    rcases direction with forward | backward
    · simp [clusterEndpoint, retainedEdge, forward, Ne.symm distinct]
    · simp [clusterEndpoint, retainedEdge, backward, Ne.symm distinct]
  apply termPositive.trans_le
  unfold degree
  exact Finset.single_le_sum (f := fun other : ClusterEdge network configuration =>
      ((if (clusterEndpoint network configuration other).1 = vertex.val then (1 : ℝ) else 0) +
        (if (clusterEndpoint network configuration other).2 = vertex.val then 1 else 0)))
    (fun other _ => by split_ifs <;> norm_num) (Finset.mem_univ retainedEdge)

theorem clusterEdge_nonempty (crossing : network.crosses configuration = true) :
    Nonempty (ClusterEdge network configuration) := by
  classical
  by_contra empty
  haveI : IsEmpty (ClusterEdge network configuration) := not_nonempty_iff.mp empty
  have positive := cluster_degree_positive network configuration crossing
    ⟨network.source, SimpleGraph.Reachable.refl _⟩
  simp only [degree, Finset.univ_eq_empty, Finset.sum_empty, lt_self_iff_false] at positive

/-- Both clocks in the manuscript, now on every vertex and edge of the
actual retained connected graph. There is no assumed degree bound and no
removal of old high-degree vertices. -/
theorem actual_full_cluster_clocks (crossing : network.crosses configuration = true)
    (scale : ℝ) (potential : RetainedSkeletonVertex network configuration → ℝ) :
    (∑ vertex, degreeWeight (clusterRetainedEndpoint network configuration) vertex *
      (-(2 * network.liveCount .connected .connected configuration * scale *
        rateOneGenerator (clusterRetainedEndpoint network configuration) potential vertex)) * potential vertex =
      scale * energy (clusterRetainedEndpoint network configuration) potential) ∧
    (∑ vertex, (1 / (Fintype.card (RetainedSkeletonVertex network configuration) : ℝ)) *
      (-((Fintype.card (RetainedSkeletonVertex network configuration) : ℝ) * scale *
        laplacian (clusterRetainedEndpoint network configuration) potential vertex)) * potential vertex =
      scale * energy (clusterRetainedEndpoint network configuration) potential) := by
  letI := clusterEdge_nonempty network configuration crossing
  letI : Nonempty (RetainedSkeletonVertex network configuration) :=
    ⟨⟨network.source, SimpleGraph.Reachable.refl _⟩⟩
  constructor
  · simpa only [clusterEdge_card] using exact_degree_clock (clusterRetainedEndpoint network configuration)
      (cluster_degree_positive network configuration crossing) scale potential
  · exact exact_counting_clock (clusterRetainedEndpoint network configuration) scale potential

theorem actual_full_cluster_reversible (crossing : network.crosses configuration = true)
    (first last : RetainedSkeletonVertex network configuration) :
    degreeWeight (clusterRetainedEndpoint network configuration) first *
      transitionKernel (clusterRetainedEndpoint network configuration) first last =
    degreeWeight (clusterRetainedEndpoint network configuration) last *
      transitionKernel (clusterRetainedEndpoint network configuration) last first :=
  detailed_balance _ (cluster_degree_positive network configuration crossing) first last

end
end IGSIII34.Diffusion
