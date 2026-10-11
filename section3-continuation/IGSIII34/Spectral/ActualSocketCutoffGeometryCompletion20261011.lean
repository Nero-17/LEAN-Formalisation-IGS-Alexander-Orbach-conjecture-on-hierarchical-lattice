import IGSIII34.Spectral.ActualCellCutoffSupportCompletion20261011
import IGSIII34.Spectral.ActualDescendantAnchorCompletion20261011
import IGSIII34.Spectral.NoncollarRootInteriorCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem block_word_append_first_coordinates_completion20261011
    {First Last : Type*} (coarse fine : ℕ)
    (parentWord : Fin (coarse + 1) → First × Last) (suffix : Fin (fine + 1) → First × Last) :
    (fun index => (blockWordAppendCompletion20261011 coarse fine parentWord suffix index).1) =
      blockWordAppendCompletion20261011 coarse fine (fun index => (parentWord index).1) (fun index => (suffix index).1) := by
  have mapped (index : Fin ((coarse + 1) + (fine + 1))) :
      (Fin.append parentWord suffix index).1 =
        Fin.append (fun index => (parentWord index).1) (fun index => (suffix index).1) index := by
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;> simp
  funext index
  exact mapped (Fin.cast (by omega) index)

theorem generation_word_edge_injective_completion20261011 (rule : Rule) (depth : ℕ) :
    Function.Injective (generationWordEdge rule depth) := by
  intro first last equality
  have addresses := congrArg (generationEdgeAddress rule depth) equality
  rw [generationWordEdge_address, generationWordEdge_address] at addresses
  exact List.ofFn_injective addresses

theorem generation_block_cell_edge_disjoint_completion20261011 (rule : Rule) (coarse fine : ℕ)
    (first last : Fin (rule.generation coarse).edges) (different : first ≠ last)
    (child other : Fin (rule.generation fine).edges) :
    (generationBlockCellEmbedding rule coarse fine first).edge child ≠
      (generationBlockCellEmbedding rule coarse fine last).edge other := by
  intro equality
  apply different
  have coded := congrArg (rule.generationBlockDecomposition coarse fine).edge equality
  change (rule.generationBlockDecomposition coarse fine).edge
      ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (first, child))) =
    (rule.generationBlockDecomposition coarse fine).edge
      ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (last, other))) at coded
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at coded
  exact congrArg Prod.fst (finProdFinEquiv.injective coded)

def physicalEdgeRootCutoffVerticesCompletion20261011 (rule : Rule) (depth : ℕ)
    (edge : Fin (rule.generation depth).edges) : Finset (Fin (rule.generation depth).vertices) :=
  {((rule.generation depth).network.endpoint edge).1, ((rule.generation depth).network.endpoint edge).2}

theorem physical_edge_root_cutoff_endpoint_values_completion20261011 (rule : Rule) (depth : ℕ)
    (edge : Fin (rule.generation depth).edges) :
    (if ((rule.generation depth).network.endpoint edge).1 ∈ physicalEdgeRootCutoffVerticesCompletion20261011 rule depth edge
      then (1 : ℝ) else 0) = 1 ∧
    (if ((rule.generation depth).network.endpoint edge).2 ∈ physicalEdgeRootCutoffVerticesCompletion20261011 rule depth edge
      then (1 : ℝ) else 0) = 1 := by
  simp [physicalEdgeRootCutoffVerticesCompletion20261011]

theorem physical_edge_root_cutoff_anchor_value_completion20261011 (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    (if componentWordAnchor rule marks depth word ∈
      physicalEdgeRootCutoffVerticesCompletion20261011 rule depth
        (generationWordEdge rule depth (fun index => (word index).1)) then (1 : ℝ) else 0) = 1 := by
  classical
  have values := physical_edge_root_cutoff_endpoint_values_completion20261011 rule depth
    (generationWordEdge rule depth (fun index => (word index).1))
  by_cases side : (retainedComponentState rule marks (List.ofFn word)).sourceSelected = true
  · simpa only [componentWordAnchor, if_pos side] using values.1
  · simpa only [componentWordAnchor, if_neg side] using values.2

theorem physical_edge_root_cutoff_projected_flat_completion20261011 (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges)
    (edge : Fin (rule.generation depth).edges) (opened : configuration edge = true) :
    sourceProjection (network (rule.generation depth).network configuration)
      (fun vertex => if vertex ∈ physicalEdgeRootCutoffVerticesCompletion20261011 rule depth edge then 1 else 0)
      ((rule.generation depth).network.endpoint edge).1 =
    sourceProjection (network (rule.generation depth).network configuration)
      (fun vertex => if vertex ∈ physicalEdgeRootCutoffVerticesCompletion20261011 rule depth edge then 1 else 0)
      ((rule.generation depth).network.endpoint edge).2 := by
  classical
  have endpoints := physical_edge_root_cutoff_endpoint_values_completion20261011 rule depth edge
  have reachable := endpoint_source_reachable_iff (network (rule.generation depth).network configuration) ⟨edge, opened⟩
  unfold sourceProjection
  dsimp only at ⊢
  rw [endpoints.1, endpoints.2]
  change (network (rule.generation depth).network configuration).graph.Reachable
      (network (rule.generation depth).network configuration).source ((rule.generation depth).network.endpoint edge).1 ↔
    (network (rule.generation depth).network configuration).graph.Reachable
      (network (rule.generation depth).network configuration).source ((rule.generation depth).network.endpoint edge).2 at reachable
  by_cases first : (network (rule.generation depth).network configuration).graph.Reachable
    (network (rule.generation depth).network configuration).source ((rule.generation depth).network.endpoint edge).1
  · rw [if_pos first, if_pos (reachable.mp first)]
  · rw [if_neg first, if_neg (mt reachable.mpr first)]

theorem actual_binary_parent_boundary_zero_outside_completion20261011
    (rule : Rule) (coarse fine : ℕ) (parent : Fin (rule.generation coarse).edges)
    (selected : Finset (Fin (rule.generation (coarse + fine + 1)).vertices))
    (internal : ∀ vertex ∈ selected, ∃ inside : (rule.generation fine).network.InteriorVertex,
      (generationBlockCellEmbedding rule coarse fine parent).vertex inside.val = vertex)
    (edge : Fin (rule.generation (coarse + fine + 1)).edges)
    (outside : ¬∃ child : Fin (rule.generation fine).edges,
      (generationBlockCellEmbedding rule coarse fine parent).edge child = edge) :
    (if ((rule.generation (coarse + fine + 1)).network.endpoint edge).1 ∈ selected then (1 : ℝ) else 0) = 0 ∧
    (if ((rule.generation (coarse + fine + 1)).network.endpoint edge).2 ∈ selected then (1 : ℝ) else 0) = 0 := by
  classical
  have noFirst : ((rule.generation (coarse + fine + 1)).network.endpoint edge).1 ∉ selected := by
    intro member
    obtain ⟨inside, equality⟩ := internal _ member
    exact outside (generation_block_internal_incident_edge_completion20261011 rule coarse fine parent inside edge (Or.inl equality.symm))
  have noLast : ((rule.generation (coarse + fine + 1)).network.endpoint edge).2 ∉ selected := by
    intro member
    obtain ⟨inside, equality⟩ := internal _ member
    exact outside (generation_block_internal_incident_edge_completion20261011 rule coarse fine parent inside edge (Or.inr equality.symm))
  simp only [if_neg noFirst, if_neg noLast, and_self]

theorem nonterminal_physical_edge_cutoff_roots_parent_interior_completion20261011
    (rule : Rule) (coarse fine : ℕ) (parent : Fin (rule.generation coarse).edges)
    (edges : Fin (fine + 1) → Fin rule.edges)
    (nonterminal : ∀ side : Bool, edges ∉ actualTerminalSocketSetCompletion20261011 rule 0 (fine + 1) side) :
    ∀ vertex ∈ physicalEdgeRootCutoffVerticesCompletion20261011 rule (coarse + fine + 1)
        ((generationBlockCellEmbedding rule coarse fine parent).edge (generationWordEdge rule fine edges)),
      ∃ inside : (rule.generation fine).network.InteriorVertex,
        (generationBlockCellEmbedding rule coarse fine parent).vertex inside.val = vertex := by
  classical
  intro vertex member
  simp only [physicalEdgeRootCutoffVerticesCompletion20261011, Finset.mem_insert, Finset.mem_singleton] at member
  rw [(generationBlockCellEmbedding rule coarse fine parent).endpoint] at member
  exact nonterminal_descendant_trace_roots_parent_interior_completion20261011 rule coarse fine parent edges nonterminal vertex member

end
end IGSIII34.Spectral
