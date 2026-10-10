import IGSIII.Chemical.SubstitutionPaths.IndexedPaths
import Universality.Percolation.ClusterMass
import Universality.Percolation.LocalLabelLaw
import IGSIII34.AO.ActualMass

/-! The terminal core is the union of the actual simple terminal paths.
Its cardinality is compared with the actual connected child count, rather
than an abstract offspring matrix. -/

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical
open IGSIII.Chemical.Substitution

def terminalCoreEdges {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Finset (Fin edges) := by
  classical
  exact (edgePathFamily network configuration).paths.biUnion id

theorem terminalCoreEdges_open_active {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) {edge : Fin edges}
    (membership : edge ∈ terminalCoreEdges network configuration) :
    configuration edge = true ∧ network.active .connected configuration (network.endpoint edge).1 = true := by
  classical
  obtain ⟨path, pathMembership, edgeMembership⟩ := Finset.mem_biUnion.mp membership
  refine ⟨edgePathFamily_used_edge network simple configuration pathMembership edgeMembership, ?_⟩
  by_cases reachable : (network.openGraph configuration).Reachable network.source network.target
  · simp only [edgePathFamily, dif_pos reachable] at pathMembership
    obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp pathMembership
    have bondUsed := (Finset.mem_filter.mp edgeMembership).2
    obtain ⟨walk, _, rfl⟩ := (mem_graphPathFamily _ _ _ reachable bondPath).mp bondMembership
    have endpointUsed := walk.fst_mem_support_of_mem_edges (List.mem_toFinset.mp bondUsed)
    have endpointReachable : (network.openGraph configuration).Reachable network.source (network.endpoint edge).1 :=
      ⟨walk.takeUntil _ endpointUsed⟩
    simpa [FiniteNetwork.active, SimpleGraph.reachableDecide_eq_true] using endpointReachable
  · simp only [edgePathFamily, dif_neg reachable, Finset.mem_singleton] at pathMembership
    simp [pathMembership] at edgeMembership

theorem terminalCoreEdges_card_le_clusterEdgeCount {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) :
    (terminalCoreEdges network configuration).card ≤ network.clusterEdgeCount .connected configuration := by
  classical
  apply Finset.card_le_card
  intro edge membership
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    terminalCoreEdges_open_active network simple configuration membership⟩

def terminalCoreMean {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (probability : ℝ) : ℝ :=
  ∑ configuration, network.conditionalCellWeight probability true configuration *
    (terminalCoreEdges network configuration).card

theorem terminalCoreMean_nonnegative {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {probability : ℝ}
    (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1) :
    0 ≤ terminalCoreMean network probability := by
  exact Finset.sum_nonneg fun configuration _ => mul_nonneg
    (network.conditionalCellWeight_nonneg nonnegative atMostOne _ _) (Nat.cast_nonneg _)

theorem terminalCoreMean_le_connected_entry {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    {probability : ℝ} (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1) :
    terminalCoreMean network probability ≤ network.massMatrix probability .connected .connected := by
  rw [← network.conditionalCellResponse_connected probability .connected,
    network.conditionalCellResponse_eq_weighted_sum]
  apply Finset.sum_le_sum
  intro configuration _
  apply mul_le_mul_of_nonneg_left _
    (network.conditionalCellWeight_nonneg nonnegative atMostOne _ _)
  rw [← network.clusterEdgeCount_eq_liveCount]
  exact_mod_cast terminalCoreEdges_card_le_clusterEdgeCount network simple configuration

theorem terminalCoreMean_strictly_below_mass_radius {rule : Rule}
    (classicalRule : rule.Classical) {probability : ℝ}
    (positive : 0 < probability) (belowOne : probability < 1) :
    terminalCoreMean rule.network probability <
      (spectralRadius ℂ ((rule.network.massMatrix probability).map Complex.ofReal)).toReal := by
  exact (terminalCoreMean_le_connected_entry rule.network classicalRule.simple positive.le belowOne.le).trans_lt
    (classicalRule.mass_spectralRadius_strictly_gt_connected_entry positive belowOne)

end
end IGSIII4
