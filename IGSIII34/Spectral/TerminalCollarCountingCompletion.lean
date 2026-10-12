import Universality.Graph.TerminalPortCounting
import IGSIII.Chemical.SmallBall.ComponentOwnershipEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open scoped BigOperators

/-- A physical terminal chain, retaining the endpoint orientation at every
substitution. It refers to host ports, not to independent percolation sides. -/
def terminalPortWeightCompletion (rule : Rule) :
    Bool → List (Fin rule.edges × Bool) → ℕ
  | _, [] => 1
  | side, choice :: tail =>
    if rule.network.edgePort choice.1 choice.2 = rule.network.terminalVertex side then
      terminalPortWeightCompletion rule choice.2 tail else 0

theorem terminalPortWeight_le_one_completion (rule : Rule)
    (side : Bool) (word : List (Fin rule.edges × Bool)) :
    terminalPortWeightCompletion rule side word ≤ 1 := by
  induction word generalizing side with
  | nil => exact le_rfl
  | cons choice tail inductionHypothesis =>
    simp only [terminalPortWeightCompletion]
    split_ifs
    · exact inductionHypothesis choice.2
    · exact Nat.zero_le _

theorem terminalPortWeight_sum_completion (rule : Rule)
    (classicalRule : rule.Classical) (depth : ℕ) (side : Bool) :
    (∑ word : Fin depth → (Fin rule.edges × Bool),
      terminalPortWeightCompletion rule side (List.ofFn word)) =
        (rule.network.fullGraph.degree rule.network.source)^depth := by
  classical
  induction depth generalizing side with
  | zero => simp [terminalPortWeightCompletion]
  | succ depth inductionHypothesis =>
    rw [← (Fin.consEquiv (fun _ : Fin (depth + 1) => Fin rule.edges × Bool)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      terminalPortWeightCompletion]
    have split : (∑ choice : Fin rule.edges × Bool, ∑ tail : Fin depth → (Fin rule.edges × Bool),
        if rule.network.edgePort choice.1 choice.2 = rule.network.terminalVertex side then
          terminalPortWeightCompletion rule choice.2 (List.ofFn tail) else 0) =
        ∑ choice : Fin rule.edges × Bool,
          if rule.network.edgePort choice.1 choice.2 = rule.network.terminalVertex side then
            (rule.network.fullGraph.degree rule.network.source)^depth else 0 := by
      apply Finset.sum_congr rfl
      intro choice _
      split_ifs with port
      · exact inductionHypothesis choice.2
      · simp only [Finset.sum_const_zero]
    rw [split, Fintype.sum_prod_type]
    calc
      _ = (∑ edge : Fin rule.edges, ∑ input : Bool,
          if rule.network.edgePort edge input = rule.network.terminalVertex side then (1 : ℕ) else 0) *
            (rule.network.fullGraph.degree rule.network.source)^depth := by
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro edge _
        apply Finset.sum_congr rfl
        intro input _
        split_ifs <;> simp
      _ = _ := by rw [classicalRule.terminal_port_row_sum, pow_succ']

theorem actual_terminal_socket_has_port_chain_completion
    (rule : Rule) (fine depth : ℕ) (word : Fin depth → Fin rule.edges)
    (vertex : Fin (rule.generation fine).vertices) (side : Bool)
    (touches : (generationComponentWordEmbedding rule fine depth word).vertex vertex =
      (rule.generation (fine + depth)).network.terminalVertex side) :
    ∃ ports : Fin depth → (Fin rule.edges × Bool),
      (∀ index, (ports index).1 = word index) ∧
      terminalPortWeightCompletion rule side (List.ofFn ports) = 1 := by
  classical
  induction depth generalizing side with
  | zero => exact ⟨fun index => Fin.elim0 index, fun index => Fin.elim0 index, rfl⟩
  | succ depth inductionHypothesis =>
    change (rule.generationCellEmbedding (fine + depth) (word 0)).vertex
      ((generationComponentWordEmbedding rule fine depth (fun index => word index.succ)).vertex vertex) = _ at touches
    rcases (rule.generationCellEmbedding_terminal_iff (fine + depth) (word 0) _ side).mp touches with
      ⟨intermediate, port⟩ | ⟨intermediate, port⟩
    · obtain ⟨tail, sameEdges, valid⟩ := inductionHypothesis
        (fun index => word index.succ) false intermediate
      refine ⟨Fin.cons (word 0, false) tail, ?_, ?_⟩
      · intro index
        refine Fin.cases ?_ (fun index => ?_) index
        · rfl
        · simpa only [Fin.cons_succ] using sameEdges index
      · simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
          terminalPortWeightCompletion, edgePort, Bool.false_eq_true, ↓reduceIte, port, valid]
    · obtain ⟨tail, sameEdges, valid⟩ := inductionHypothesis
        (fun index => word index.succ) true intermediate
      refine ⟨Fin.cons (word 0, true) tail, ?_, ?_⟩
      · intro index
        refine Fin.cases ?_ (fun index => ?_) index
        · rfl
        · simpa only [Fin.cons_succ] using sameEdges index
      · simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
          terminalPortWeightCompletion, edgePort, ↓reduceIte, port, valid]

/-- The actual physical descendant sockets incident with one planted
terminal number at most d^n, uniformly in the fine generation. -/
theorem actual_terminal_socket_count_bound_completion
    (rule : Rule) (classicalRule : rule.Classical) (fine depth : ℕ) (side : Bool) :
    (Finset.univ.filter (fun word : Fin depth → Fin rule.edges =>
      ∃ vertex : Fin (rule.generation fine).vertices,
        (generationComponentWordEmbedding rule fine depth word).vertex vertex =
          (rule.generation (fine + depth)).network.terminalVertex side)).card ≤
      (rule.network.fullGraph.degree rule.network.source)^depth := by
  classical
  let ports := Finset.univ.filter (fun ports : Fin depth → (Fin rule.edges × Bool) =>
    terminalPortWeightCompletion rule side (List.ofFn ports) = 1)
  have inclusion : Finset.univ.filter (fun word : Fin depth → Fin rule.edges =>
      ∃ vertex : Fin (rule.generation fine).vertices,
        (generationComponentWordEmbedding rule fine depth word).vertex vertex =
          (rule.generation (fine + depth)).network.terminalVertex side) ⊆
      ports.image (fun ports index => (ports index).1) := by
    intro word member
    obtain ⟨vertex, touches⟩ := (Finset.mem_filter.mp member).2
    obtain ⟨portWord, sameEdges, valid⟩ :=
      actual_terminal_socket_has_port_chain_completion rule fine depth word vertex side touches
    exact Finset.mem_image.mpr ⟨portWord, Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid⟩, funext sameEdges⟩
  have count : ports.card = ∑ word : Fin depth → (Fin rule.edges × Bool),
      terminalPortWeightCompletion rule side (List.ofFn word) := by
    simp only [ports, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro word _
    have bound := terminalPortWeight_le_one_completion rule side (List.ofFn word)
    split_ifs <;> omega
  exact (Finset.card_le_card inclusion).trans
    ((Finset.card_image_le).trans (by rw [count, terminalPortWeight_sum_completion rule classicalRule]))

end
end IGSIII34.Spectral
