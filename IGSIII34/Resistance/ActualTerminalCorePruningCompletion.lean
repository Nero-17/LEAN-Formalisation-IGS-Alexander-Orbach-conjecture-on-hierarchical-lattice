import IGSIII4.CoreGeometry
import IGSIII34.Resistance.OhmicCurrentTerminalPathCompletion
import IGSIII34.Resistance.SupportedCurrentPruningCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution
open IGSIII34.Resistance IGSIII34.Resistance.FiniteNetwork IGSIII4

theorem terminalCoreEdges_contains_simple_walk_edge_completion
    {vertices edges : ℕ} (host : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (path : (host.openGraph configuration).Walk host.source host.target) (simple : path.IsPath)
    (edge : Fin edges) (contains : s((host.endpoint edge).1, (host.endpoint edge).2) ∈ path.edges) :
    edge ∈ terminalCoreEdges host configuration := by
  classical
  have reachable : (host.openGraph configuration).Reachable host.source host.target := ⟨path⟩
  have pathMember : path.edges.toFinset ∈ (graphPathFamily (host.openGraph configuration) host.source host.target reachable).paths :=
    (mem_graphPathFamily _ _ _ reachable _).mpr ⟨path, simple, rfl⟩
  have indexedMember : indexedPath host path.edges.toFinset ∈ (edgePathFamily host configuration).paths := by
    simp only [edgePathFamily, dif_pos reachable]
    exact Finset.mem_image.mpr ⟨path.edges.toFinset, pathMember, rfl⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨indexedPath host path.edges.toFinset, indexedMember, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.mem_toFinset.mpr contains⟩

theorem unitConfigurationResistance_terminal_core_pruning_completion
    {vertices edges : ℕ} (host : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((host.endpoint edge).1, (host.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : host.crosses configuration = true) :
    unitConfigurationResistance host (terminalCoreConfiguration host configuration) = unitConfigurationResistance host configuration := by
  classical
  let original := network host configuration
  let retained := network host (terminalCoreConfiguration host configuration)
  let inclusion : {edge : Fin edges // terminalCoreConfiguration host configuration edge = true} →
      {edge : Fin edges // configuration edge = true} := fun edge =>
    ⟨edge.val, (terminalCoreEdges_open_active host simple configuration
      (of_decide_eq_true edge.property)).1⟩
  have injective : Function.Injective inclusion := by
    intro first last equal
    apply Subtype.ext
    exact congrArg (fun edge : {edge : Fin edges // configuration edge = true} => edge.val) equal
  obtain ⟨current, unitFlow, minimal⟩ := original.exists_minimizing_unitFlow_of_connected
    (connected_of_crosses host configuration crossing) (fun _ => zero_lt_one)
  obtain ⟨potential, ohm⟩ := original.minimizing_current_has_potential (fun _ => zero_lt_one) unitFlow minimal
  have supported : ∀ edge ∉ Set.range inclusion, current edge = 0 := by
    intro edge outside
    by_contra nonzero
    have actualPath : ∃ path : (host.openGraph configuration).Walk host.source host.target,
        path.IsPath ∧ s((host.endpoint edge.val).1, (host.endpoint edge.val).2) ∈ path.edges := by
      have witnessed := nonzero_ohmic_current_terminal_path_completion
        original (fun _ => 1) current potential (fun _ => zero_lt_one) unitFlow ohm edge nonzero
      change (∃ path : (network host configuration).graph.Walk host.source host.target,
        path.IsPath ∧ s((host.endpoint edge.val).1, (host.endpoint edge.val).2) ∈ path.edges) at witnessed
      rwa [graph_eq_openGraph] at witnessed
    obtain ⟨path, pathSimple, contains⟩ := actualPath
    have member := terminalCoreEdges_contains_simple_walk_edge_completion host configuration path pathSimple edge.val contains
    have opened : terminalCoreConfiguration host configuration edge.val = true := decide_eq_true member
    exact outside ⟨⟨edge.val, opened⟩, Subtype.ext rfl⟩
  have preservation := effectiveResistance_supported_current_pruning_completion original retained inclusion injective
    (fun _ => rfl) rfl rfl (fun _ => 1) current (fun _ => zero_le_one) unitFlow minimal supported
  exact preservation

/-- The formerly accepted Section 3 pruning interface is now obtained from
the actual finite-network electrical proof at every generation. -/
theorem classical_actual_core_pruning_section_three_completion
    (rule : Rule) (classicalRule : rule.Classical) : AcceptedCorePruningSectionThree rule := by
  refine ⟨?_⟩
  intro depth configuration crossing
  exact unitConfigurationResistance_terminal_core_pruning_completion (rule.generation depth).network
    (classicalRule.generation depth).simple configuration crossing

end
end IGSIII34.Percolation
