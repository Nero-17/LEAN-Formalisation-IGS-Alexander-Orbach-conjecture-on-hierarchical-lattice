import IGSIII.Probability.CountableInvariantFamily
import IGSIII.Probability.CompactApproximation
import Mathlib.Topology.Sequences
import Mathlib.Topology.ClusterPt

set_option autoImplicit false

namespace IGSIII.Probability

open Set Filter
open scoped Topology

variable {Space : Type*} [MetricSpace Space]

def orbitClusterSet (sequence : ℕ → Space) : Set Space :=
  {point | MapClusterPt point atTop sequence}

theorem orbitClusterSet_nonempty (sequence : ℕ → Space)
    (precompact : IsCompact (closure (Set.range sequence))) :
    (orbitClusterSet sequence).Nonempty := by
  obtain ⟨point, _, subsequence, increasing, convergence⟩ :=
    precompact.tendsto_subseq (fun depth => subset_closure ⟨depth, rfl⟩)
  exact ⟨point, MapClusterPt.of_comp increasing.tendsto_atTop convergence.mapClusterPt⟩

theorem orbitClusterSet_compact (sequence : ℕ → Space)
    (precompact : IsCompact (closure (Set.range sequence))) :
    IsCompact (orbitClusterSet sequence) := by
  apply precompact.of_isClosed_subset (isClosed_setOf_clusterPt (f := Filter.map sequence atTop))
  intro point cluster
  exact isClosed_closure.mem_of_mapClusterPt cluster
    (Filter.Eventually.of_forall (fun depth => subset_closure ⟨depth, rfl⟩))

theorem orbitClusterSet_forward (map : Space → Space) (continuous : Continuous map)
    (sequence : ℕ → Space) (recursion : ∀ depth, sequence (depth + 1) = map (sequence depth)) :
    Set.MapsTo map (orbitClusterSet sequence) (orbitClusterSet sequence) := by
  intro point cluster
  have imageCluster := cluster.continuousAt_comp continuous.continuousAt
  have sameShift : (map ∘ sequence) = sequence ∘ (fun depth => depth + 1) := by
    funext depth
    exact (recursion depth).symm
  rw [sameShift, mapClusterPt_comp, Filter.map_add_atTop_eq_nat] at imageCluster
  exact imageCluster

theorem orbitClusterSet_onto (map : Space → Space) (continuous : Continuous map)
    (sequence : ℕ → Space) (recursion : ∀ depth, sequence (depth + 1) = map (sequence depth))
    (precompact : IsCompact (closure (Set.range sequence))) :
    Set.SurjOn map (orbitClusterSet sequence) (orbitClusterSet sequence) := by
  intro point cluster
  have shiftedCluster : MapClusterPt point atTop (sequence ∘ (fun depth => depth + 1)) := by
    rw [mapClusterPt_comp, Filter.map_add_atTop_eq_nat]
    exact cluster
  obtain ⟨subsequence, increasing, convergence⟩ := shiftedCluster.tendsto_subseq
  obtain ⟨predecessor, _, subsubsequence, subIncreasing, predecessorConvergence⟩ :=
    precompact.tendsto_subseq (fun depth => subset_closure ⟨subsequence depth, rfl⟩)
  refine ⟨predecessor, ?_, ?_⟩
  · exact MapClusterPt.of_comp (increasing.tendsto_atTop.comp subIncreasing.tendsto_atTop) predecessorConvergence.mapClusterPt
  · have imageConvergence := continuous.tendsto predecessor |>.comp predecessorConvergence
    have targetConvergence := convergence.comp subIncreasing.tendsto_atTop
    apply tendsto_nhds_unique imageConvergence
    convert targetConvergence using 1
    funext depth
    exact (recursion (subsequence (subsubsequence depth))).symm

end IGSIII.Probability

