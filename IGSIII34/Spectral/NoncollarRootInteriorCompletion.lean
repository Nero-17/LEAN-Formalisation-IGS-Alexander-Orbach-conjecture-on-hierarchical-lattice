import IGSIII34.Spectral.ActualDescendantAnchorCompletion
import IGSIII34.Spectral.ActualCollarExpectationCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators _root_.Topology

/-- If a descendant socket does not touch either planted terminal, both
of the corresponding trace edge's roots are actual internal parent points. -/
theorem nonterminal_socket_trace_roots_internal_completion
    (rule : Rule) (fine : ℕ) (edges : Fin (fine + 1) → Fin rule.edges)
    (nonterminal : ∀ side : Bool, edges ∉ actualTerminalSocketSetCompletion rule 0 (fine + 1) side) :
    (((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).1 ≠
        (rule.generation fine).network.source ∧
      ((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).1 ≠
        (rule.generation fine).network.target) ∧
    (((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).2 ≠
        (rule.generation fine).network.source ∧
      ((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).2 ≠
        (rule.generation fine).network.target) := by
  classical
  have excludes (rootSide terminalSide : Bool)
      (touches : (if rootSide then ((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).1
          else ((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).2) =
        (plantedVertex (rule.generation fine).network terminalSide)) : False := by
    apply nonterminal (!terminalSide)
    unfold actualTerminalSocketSetCompletion
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have embeddingEquality := generationComponentWordEmbedding_zero rule fine edges
    refine ⟨plantedVertex (rule.generation 0).network rootSide, ?_⟩
    have predicateEquality := dependentMap_heq
      (fun host (embedding : (rule.generation 0).network.NetworkEmbedding (rule.generation host).network) =>
        embedding.vertex (plantedVertex (rule.generation 0).network rootSide) =
          (rule.generation host).network.terminalVertex (!terminalSide))
      (Nat.zero_add (fine + 1)) embeddingEquality
    rw [eq_of_heq predicateEquality]
    change (generationWordVertexEmbedding rule fine edges).vertex (plantedVertex rule.network rootSide) = _
    rw [generationAddressEmbedding_word_planted, touches, generationOldVertex_planted]
    cases terminalSide <;> rfl
  constructor
  · constructor
    · intro touches
      exact excludes true true touches
    · intro touches
      exact excludes true false touches
  · constructor
    · intro touches
      exact excludes false true touches
    · intro touches
      exact excludes false false touches

theorem nonterminal_descendant_trace_roots_parent_interior_completion
    (rule : Rule) (coarse fine : ℕ) (parent : Fin (rule.generation coarse).edges)
    (edges : Fin (fine + 1) → Fin rule.edges)
    (nonterminal : ∀ side : Bool, edges ∉ actualTerminalSocketSetCompletion rule 0 (fine + 1) side) :
    ∀ root : Fin (rule.generation (coarse + fine + 1)).vertices,
      root = (generationBlockCellEmbedding rule coarse fine parent).vertex
          ((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).1 ∨
        root = (generationBlockCellEmbedding rule coarse fine parent).vertex
          ((rule.generation fine).network.endpoint (generationWordEdge rule fine edges)).2 →
      ∃ inside : (rule.generation fine).network.InteriorVertex,
        (generationBlockCellEmbedding rule coarse fine parent).vertex inside.val = root := by
  intro root endpoint
  have interior := nonterminal_socket_trace_roots_internal_completion rule fine edges nonterminal
  rcases endpoint with first | last
  · exact ⟨⟨_, interior.1⟩, first.symm⟩
  · exact ⟨⟨_, interior.2⟩, last.symm⟩

end
end IGSIII34.Spectral
