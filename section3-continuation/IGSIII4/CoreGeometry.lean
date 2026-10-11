import IGSIII4.CoreMinimalCharacterization
import IGSIII34.Resistance.DistanceEnergy
import IGSIII34.Percolation.ElectricalTransfer
import IGSIII.Chemical.SubstitutionPaths.BlockPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution
open IGSIII34.Percolation IGSIII34.Resistance IGSIII34.Resistance.FiniteNetwork

def terminalCoreConfiguration {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Configuration edges :=
  configurationOfPath (terminalCoreEdges network configuration)

theorem terminalCoreConfiguration_crosses {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    network.crosses (terminalCoreConfiguration network configuration) = true := by
  classical
  obtain ⟨path, membership⟩ := (edgePathFamily network configuration).nonempty
  have minimal := edgePathFamily_member_minimal network simple configuration crossing membership
  apply network.crosses_mono (configurationOfPath path) _ _ minimal.1
  intro edge opened
  exact decide_eq_true (Finset.mem_biUnion.mpr ⟨path, membership, of_decide_eq_true opened⟩)

theorem terminalCoreConfiguration_paths {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    (edgePathFamily network (terminalCoreConfiguration network configuration)).paths =
      (edgePathFamily network configuration).paths := by
  classical
  ext path
  constructor
  · intro membership
    apply edgePathFamily_mono network (terminalCoreConfiguration network configuration) configuration _
      (terminalCoreConfiguration_crosses network simple configuration crossing) membership
    intro edge opened
    exact (terminalCoreEdges_open_active network simple configuration (of_decide_eq_true opened)).1
  · intro membership
    apply (edgePathFamily_mem_iff_minimal network simple _
      (terminalCoreConfiguration_crosses network simple configuration crossing) path).mpr
    exact ⟨edgePathFamily_member_minimal network simple configuration crossing membership,
      fun edge used => decide_eq_true (Finset.mem_biUnion.mpr ⟨path, membership, used⟩)⟩

theorem terminalCoreConfiguration_distance {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    (network.openGraph (terminalCoreConfiguration network configuration)).dist network.source network.target =
      (network.openGraph configuration).dist network.source network.target := by
  have shortestSame : (edgePathFamily network (terminalCoreConfiguration network configuration)).shortest (fun _ => 1) =
      (edgePathFamily network configuration).shortest (fun _ => 1) := by
    simp only [PathFamily.shortest, terminalCoreConfiguration_paths network simple configuration crossing]
  rw [edgePathFamily_shortest_unit network simple, edgePathFamily_shortest_unit network simple] at shortestSame
  exact_mod_cast shortestSame

theorem terminalCore_distance_sq_le_count_mul_resistance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    (resistancePreserved : unitConfigurationResistance network (terminalCoreConfiguration network configuration) =
      unitConfigurationResistance network configuration) :
    ((network.openGraph configuration).dist network.source network.target : ℝ) ^ 2 ≤
      (terminalCoreEdges network configuration).card * unitConfigurationResistance network configuration := by
  classical
  have bound := (IGSIII34.Percolation.network network (terminalCoreConfiguration network configuration)).distance_sq_le_edge_count_mul_unitResistance
    (connected_of_crosses network _ (terminalCoreConfiguration_crosses network simple configuration crossing))
  rw [graph_eq_openGraph] at bound
  change ((network.openGraph (terminalCoreConfiguration network configuration)).dist network.source network.target : ℝ) ^ 2 ≤
    (Fintype.card {edge : Fin edges // terminalCoreConfiguration network configuration edge = true} : ℝ) *
      unitConfigurationResistance network (terminalCoreConfiguration network configuration) at bound
  rw [terminalCoreConfiguration_distance network simple configuration crossing] at bound
  have cardinality : Fintype.card {edge : Fin edges // terminalCoreConfiguration network configuration edge = true} =
      (terminalCoreEdges network configuration).card := by
    simp only [terminalCoreConfiguration, configurationOfPath, decide_eq_true_eq]
    exact Fintype.card_coe _
  change ((network.openGraph configuration).dist network.source network.target : ℝ) ^ 2 ≤
    (Fintype.card {edge : Fin edges // terminalCoreConfiguration network configuration edge = true} : ℝ) *
      unitConfigurationResistance network (terminalCoreConfiguration network configuration) at bound
  rwa [cardinality, resistancePreserved] at bound

/-- Section 3's explicit pruning assertion, restricted to actual finite
generations. This is accepted by the user together with all Section 3 results.
It asserts resistance preservation only, not the Section 4 energy inequality. -/
structure AcceptedCorePruningSectionThree (rule : Rule) : Prop where
  resistancePreserved : ∀ depth (configuration : Configuration (rule.generation depth).edges),
    (rule.generation depth).network.crosses configuration = true →
    unitConfigurationResistance (rule.generation depth).network
      (terminalCoreConfiguration (rule.generation depth).network configuration) =
      unitConfigurationResistance (rule.generation depth).network configuration

end
end IGSIII4
