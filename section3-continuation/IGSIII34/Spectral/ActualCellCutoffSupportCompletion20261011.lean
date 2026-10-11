import IGSIII34.Spectral.ActualBinaryCutoffEnergyCompletion20261011
import IGSIII.Geometry.ActualBlockCellEmbedding
import Universality.Graph.InternalCellNeighborhood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators Topology

/-- A genuinely internal vertex of a physical coarse cell has no incident
edge outside the image of that cell, even after the block relabelling. -/
theorem generation_block_internal_incident_edge_completion20261011
    (rule : Rule) (coarse fine : ℕ) (parent : Fin (rule.generation coarse).edges)
    (vertex : (rule.generation fine).network.InteriorVertex)
    (edge : Fin (rule.generation (coarse + fine + 1)).edges)
    (incident : ((rule.generation (coarse + fine + 1)).network.endpoint edge).1 =
        (generationBlockCellEmbedding rule coarse fine parent).vertex vertex.val ∨
      ((rule.generation (coarse + fine + 1)).network.endpoint edge).2 =
        (generationBlockCellEmbedding rule coarse fine parent).vertex vertex.val) :
    ∃ child : Fin (rule.generation fine).edges,
      (generationBlockCellEmbedding rule coarse fine parent).edge child = edge := by
  let equivalence := rule.generationBlockDecomposition coarse fine
  have endpoint := equivalence.endpoint edge
  have lifted :
      (((rule.generation coarse).network.substitute (rule.generation fine).network).endpoint
        (equivalence.edge edge)).1 =
          ((rule.generation coarse).network.cellNetworkEmbedding (rule.generation fine).network parent).vertex vertex.val ∨
      (((rule.generation coarse).network.substitute (rule.generation fine).network).endpoint
        (equivalence.edge edge)).2 =
          ((rule.generation coarse).network.cellNetworkEmbedding (rule.generation fine).network parent).vertex vertex.val := by
    rw [endpoint]
    rcases incident with first | last
    · left
      rw [first]
      exact equivalence.vertex.apply_symm_apply _
    · right
      rw [last]
      exact equivalence.vertex.apply_symm_apply _
  obtain ⟨child, equality⟩ :=
    (rule.generation coarse).network.cell_internal_incident_edge (rule.generation fine).network
      parent vertex (equivalence.edge edge) lifted
  refine ⟨child, ?_⟩
  apply equivalence.edge.injective
  change equivalence.edge (equivalence.edge.symm
      (((rule.generation coarse).network.cellNetworkEmbedding (rule.generation fine).network parent).edge child)) = _
  simpa only [Equiv.apply_symm_apply] using equality

def openedCellEdgeEmbeddingCompletion20261011
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    {outer : Universality.FiniteNetwork outerVertices outerEdges}
    {inner : Universality.FiniteNetwork innerVertices innerEdges}
    (embedding : inner.NetworkEmbedding outer) (configuration : Configuration outerEdges) :
    {edge : Fin innerEdges // embedding.restrict configuration edge = true} ↪
      {edge : Fin outerEdges // configuration edge = true} where
  toFun edge := ⟨embedding.edge edge.val, edge.property⟩
  inj' := by
    intro first last equality
    exact Subtype.ext (embedding.edge.injective (congrArg Subtype.val equality))

def openedCellEdgeSupportCompletion20261011
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    {outer : Universality.FiniteNetwork outerVertices outerEdges}
    {inner : Universality.FiniteNetwork innerVertices innerEdges}
    (embedding : inner.NetworkEmbedding outer) (configuration : Configuration outerEdges) :
    Finset {edge : Fin outerEdges // configuration edge = true} := by
  classical
  exact Finset.univ.map (openedCellEdgeEmbeddingCompletion20261011 embedding configuration)

theorem opened_cell_edge_support_mem_completion20261011
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    {outer : Universality.FiniteNetwork outerVertices outerEdges}
    {inner : Universality.FiniteNetwork innerVertices innerEdges}
    (embedding : inner.NetworkEmbedding outer) (configuration : Configuration outerEdges)
    (edge : {edge : Fin outerEdges // configuration edge = true}) :
    edge ∈ openedCellEdgeSupportCompletion20261011 embedding configuration ↔
      ∃ child : Fin innerEdges, embedding.edge child = edge.val := by
  classical
  constructor
  · intro member
    obtain ⟨child, _, equality⟩ := Finset.mem_map.mp member
    exact ⟨child.val, congrArg Subtype.val equality⟩
  · rintro ⟨child, equality⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨child, ?_⟩, Finset.mem_univ _, ?_⟩
    · change configuration (embedding.edge child) = true
      rw [equality]
      exact edge.property
    · apply Subtype.ext
      exact equality

theorem opened_cell_edge_support_card_completion20261011
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    {outer : Universality.FiniteNetwork outerVertices outerEdges}
    {inner : Universality.FiniteNetwork innerVertices innerEdges}
    (embedding : inner.NetworkEmbedding outer) (configuration : Configuration outerEdges) :
    (openedCellEdgeSupportCompletion20261011 embedding configuration).card ≤ innerEdges := by
  classical
  unfold openedCellEdgeSupportCompletion20261011
  rw [Finset.card_map, Finset.card_univ]
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)

/-- A binary finite boundary supported on actual internal vertices of a
parent cell has all its varying opened edges in that same physical cell. -/
theorem actual_binary_cell_boundary_supported_completion20261011
    (rule : Rule) (coarse fine : ℕ) (parent : Fin (rule.generation coarse).edges)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (selected : Finset (Fin (rule.generation (coarse + fine + 1)).vertices))
    (internal : ∀ vertex ∈ selected,
      ∃ inside : (rule.generation fine).network.InteriorVertex,
        (generationBlockCellEmbedding rule coarse fine parent).vertex inside.val = vertex)
    (edge : {edge : Fin (rule.generation (coarse + fine + 1)).edges // configuration edge = true})
    (outside : edge ∉ openedCellEdgeSupportCompletion20261011
      (generationBlockCellEmbedding rule coarse fine parent) configuration) :
    (if ((rule.generation (coarse + fine + 1)).network.endpoint edge.val).1 ∈ selected then (1 : ℝ) else 0) =
      (if ((rule.generation (coarse + fine + 1)).network.endpoint edge.val).2 ∈ selected then (1 : ℝ) else 0) := by
  classical
  have noFirst : ((rule.generation (coarse + fine + 1)).network.endpoint edge.val).1 ∉ selected := by
    intro member
    obtain ⟨inside, equality⟩ := internal _ member
    apply outside
    apply (opened_cell_edge_support_mem_completion20261011 _ configuration edge).mpr
    exact generation_block_internal_incident_edge_completion20261011 rule coarse fine parent inside edge.val
      (Or.inl equality.symm)
  have noLast : ((rule.generation (coarse + fine + 1)).network.endpoint edge.val).2 ∉ selected := by
    intro member
    obtain ⟨inside, equality⟩ := internal _ member
    apply outside
    apply (opened_cell_edge_support_mem_completion20261011 _ configuration edge).mpr
    exact generation_block_internal_incident_edge_completion20261011 rule coarse fine parent inside edge.val
      (Or.inr equality.symm)
  simp only [if_neg noFirst, if_neg noLast]

theorem actual_opened_cell_edge_support_count_completion20261011
    (rule : Rule) (coarse fine : ℕ) (parent : Fin (rule.generation coarse).edges)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges) :
    (openedCellEdgeSupportCompletion20261011
      (generationBlockCellEmbedding rule coarse fine parent) configuration).card ≤ rule.edges^(fine + 1) := by
  rw [← rule.generation_edges fine]
  exact opened_cell_edge_support_card_completion20261011 _ configuration

end
end IGSIII34.Spectral
