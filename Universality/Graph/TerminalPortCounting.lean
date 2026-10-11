import Universality.Graph.GenerationTerminalEmbedding
import Universality.Graph.InternalIncidentEdges
import Universality.Graph.IncidentDegree
import Universality.Graph.ClassicalRule

namespace Universality.FiniteNetwork
noncomputable section
attribute [local instance] Classical.propDecidable
variable {vertices edges : ℕ}

/-- The two physical terminals; false is the source and true the target. -/
def terminalVertex (R : FiniteNetwork vertices edges) (side : Bool) : Fin vertices :=
  if side then R.target else R.source

/-- The physical endpoint receiving the selected child terminal. -/
def edgePort (R : FiniteNetwork vertices edges) (edge : Fin edges) (side : Bool) : Fin vertices :=
  if side then (R.endpoint edge).2 else (R.endpoint edge).1

theorem incidentEdges_symmetry_card (R : FiniteNetwork vertices edges)
    (symmetry : R.NetworkSymmetry) (vertex : Fin vertices) :
    (R.incidentEdges vertex).card = (R.incidentEdges (symmetry.vertex vertex)).card := by
  apply Finset.card_equiv symmetry.edge
  intro edge
  simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases symmetry.endpoint edge with h | h
  · rw [h]
    simp only [Equiv.apply_eq_iff_eq]
  · rw [h]
    simp only [Equiv.apply_eq_iff_eq, or_comm]

/-- Count the possible child-terminal inputs for a fixed parent output.
The orientation is output row, input column. -/
theorem terminal_port_row_sum (R : FiniteNetwork vertices edges) (side : Bool) :
    (∑ edge : Fin edges, ∑ input : Bool,
      if R.edgePort edge input = R.terminalVertex side then (1 : ℕ) else 0) =
      (R.incidentEdges (R.terminalVertex side)).card := by
  calc
    _ = ∑ edge : Fin edges,
        if (R.endpoint edge).1 = R.terminalVertex side ∨
          (R.endpoint edge).2 = R.terminalVertex side then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      simp only [Fintype.sum_bool, edgePort, Bool.false_eq_true, ↓reduceIte]
      by_cases hfirst : (R.endpoint edge).1 = R.terminalVertex side
      · have hsecond : (R.endpoint edge).2 ≠ R.terminalVertex side :=
          fun hh => R.loopless edge (hfirst.trans hh.symm)
        simp [hfirst, hsecond]
      · by_cases hsecond : (R.endpoint edge).2 = R.terminalVertex side <;>
          simp [hfirst, hsecond]
    _ = _ := by simp only [incidentEdges, Finset.sum_boole, Nat.cast_id]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem Classical.terminal_port_row_sum {rule : Rule} (h : rule.Classical) (side : Bool) :
    (∑ edge : Fin rule.edges, ∑ input : Bool,
      if rule.network.edgePort edge input = rule.network.terminalVertex side then (1 : ℕ) else 0) =
      rule.network.fullGraph.degree rule.network.source := by
  classical
  rw [rule.network.terminal_port_row_sum]
  cases side with
  | false => exact rule.network.sourceIncidentEdges_card_eq_degree h.simple
  | true =>
    obtain ⟨symmetry, hs, _⟩ := h.massAdmissible.symmetric
    have hh := rule.network.incidentEdges_symmetry_card symmetry rule.network.source
    rw [hs] at hh
    exact hh.symm.trans (rule.network.sourceIncidentEdges_card_eq_degree h.simple)

/-- A child vertex can hit a parent terminal only through a child terminal
and the corresponding physical edge endpoint. -/
theorem generationCellEmbedding_terminal_iff (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (vertex : Fin (rule.generation depth).vertices) (side : Bool) :
    (rule.generationCellEmbedding depth edge).vertex vertex =
        (rule.generation (depth + 1)).network.terminalVertex side ↔
      (vertex = (rule.generation depth).network.source ∧
        (rule.network.endpoint edge).1 = rule.network.terminalVertex side) ∨
      (vertex = (rule.generation depth).network.target ∧
        (rule.network.endpoint edge).2 = rule.network.terminalVertex side) := by
  classical
  by_cases hsource : vertex = (rule.generation depth).network.source
  · subst vertex
    cases side <;>
      simp [terminalVertex, (rule.generation depth).network.terminals_distinct,
        rule.generationCellEmbedding_source_eq_source_iff,
        rule.generationCellEmbedding_source_eq_target_iff]
  · by_cases htarget : vertex = (rule.generation depth).network.target
    · subst vertex
      cases side <;>
        simp [terminalVertex, (rule.generation depth).network.terminals_distinct.symm,
          rule.generationCellEmbedding_target_eq_source_iff,
          rule.generationCellEmbedding_target_eq_target_iff]
    · have hinternal := rule.generationCellEmbedding_internal depth edge ⟨vertex, hsource, htarget⟩
      cases side <;> simp [terminalVertex, hsource, htarget, hinternal.1, hinternal.2]

end
end Universality.Rule
