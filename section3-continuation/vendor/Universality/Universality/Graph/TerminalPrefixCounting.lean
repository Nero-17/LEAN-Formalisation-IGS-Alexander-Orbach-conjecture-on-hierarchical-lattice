import Universality.Graph.TerminalPortCounting
import Universality.Graph.AncestralStageRootLaw

namespace Universality.Rule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

/-- The actual ancestral embedding determined by a finite address prefix. -/
def ancestralVertexPrefix (rule : Rule) (age : ℕ)
    (vertex : Fin (rule.generation age).vertices) :
    (n : ℕ) → (Fin n → Fin rule.edges) → Fin (rule.generation (age + n)).vertices
  | 0, _ => vertex
  | n + 1, word => (rule.generationCellEmbedding (age + n) (word (Fin.last n))).vertex
      (rule.ancestralVertexPrefix age vertex n (Fin.init word))

theorem ancestralVertexPrefix_eq_stageRoot (rule : Rule) (age n : ℕ)
    (vertex : Fin (rule.generation age).vertices) (address : ℕ → Fin rule.edges) :
    rule.ancestralVertexPrefix age vertex n (fun i => address i.val) =
      rule.ancestralRootAtStage age n (vertex, address) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (rule.generationCellEmbedding (age + n) (address n)).vertex
      (rule.ancestralVertexPrefix age vertex n (fun i => address i.val)) = _
    rw [ih]
    simp only [ancestralRootAtStage, NetworkTower.vertexMap, Nat.leRecOn_succ (Nat.zero_le n)]
    rfl

def terminalPrefixCount (rule : Rule) (age : ℕ)
    (vertex : Fin (rule.generation age).vertices) (n : ℕ) (side : Bool) : ℕ :=
  ∑ word : Fin n → Fin rule.edges,
    if rule.ancestralVertexPrefix age vertex n word =
      (rule.generation (age + n)).network.terminalVertex side then 1 else 0

theorem generation_terminal_indicator_le (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (vertex : Fin (rule.generation depth).vertices) (side : Bool) :
    (if (rule.generationCellEmbedding depth edge).vertex vertex =
      (rule.generation (depth + 1)).network.terminalVertex side then (1 : ℕ) else 0) ≤
    ∑ input : Bool, if rule.network.edgePort edge input = rule.network.terminalVertex side then
      (if vertex = (rule.generation depth).network.terminalVertex input then 1 else 0) else 0 := by
  by_cases heq : (rule.generationCellEmbedding depth edge).vertex vertex =
      (rule.generation (depth + 1)).network.terminalVertex side
  · rw [if_pos heq]
    rcases (rule.generationCellEmbedding_terminal_iff depth edge vertex side).mp heq with
      ⟨hvertex, hport⟩ | ⟨hvertex, hport⟩
    · have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun input : Bool => if rule.network.edgePort edge input = rule.network.terminalVertex side then
          (if vertex = (rule.generation depth).network.terminalVertex input then (1 : ℕ) else 0) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ false)
      simpa only [edgePort, terminalVertex, Bool.false_eq_true, ↓reduceIte,
        hport, hvertex, if_pos, ite_true] using hh
    · have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun input : Bool => if rule.network.edgePort edge input = rule.network.terminalVertex side then
          (if vertex = (rule.generation depth).network.terminalVertex input then (1 : ℕ) else 0) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ true)
      simpa only [edgePort, terminalVertex, ↓reduceIte, hport, hvertex, if_pos, ite_true] using hh
  · simp only [heq, ↓reduceIte, Nat.zero_le]

/-- For a fixed initial vertex, each output-terminal row has at most d^n
surviving words. This uses row sums, not a false one-step conditional bound. -/
theorem Classical.terminalPrefixCount_le {rule : Rule} (h : rule.Classical)
    (age : ℕ) (vertex : Fin (rule.generation age).vertices) (n : ℕ) (side : Bool) :
    rule.terminalPrefixCount age vertex n side ≤
      (rule.network.fullGraph.degree rule.network.source) ^ n := by
  induction n generalizing side with
  | zero =>
    simp only [terminalPrefixCount, Fintype.sum_unique, ancestralVertexPrefix, pow_zero]
    split_ifs <;> omega
  | succ n ih =>
    have hsplit : rule.terminalPrefixCount age vertex (n + 1) side =
        ∑ edge : Fin rule.edges, ∑ word : Fin n → Fin rule.edges,
          if (rule.generationCellEmbedding (age + n) edge).vertex
              (rule.ancestralVertexPrefix age vertex n word) =
            (rule.generation (age + (n + 1))).network.terminalVertex side then 1 else 0 := by
      unfold terminalPrefixCount
      rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin rule.edges)).sum_comp
        (fun word => if rule.ancestralVertexPrefix age vertex (n + 1) word =
          (rule.generation (age + (n + 1))).network.terminalVertex side then (1 : ℕ) else 0),
        Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro edge _
      apply Finset.sum_congr rfl
      intro word _
      change (if rule.ancestralVertexPrefix age vertex (n + 1) (Fin.snoc word edge) = _ then _ else _) = _
      simp only [ancestralVertexPrefix, Fin.init_snoc, Fin.snoc_last]
    rw [hsplit]
    calc
      _ ≤ ∑ edge : Fin rule.edges, ∑ word : Fin n → Fin rule.edges, ∑ input : Bool,
          if rule.network.edgePort edge input = rule.network.terminalVertex side then
            (if rule.ancestralVertexPrefix age vertex n word =
              (rule.generation (age + n)).network.terminalVertex input then 1 else 0) else 0 := by
        apply Finset.sum_le_sum
        intro edge _
        apply Finset.sum_le_sum
        intro word _
        exact rule.generation_terminal_indicator_le (age + n) edge _ side
      _ = ∑ edge : Fin rule.edges, ∑ input : Bool,
          if rule.network.edgePort edge input = rule.network.terminalVertex side then
            rule.terminalPrefixCount age vertex n input else 0 := by
        apply Finset.sum_congr rfl
        intro edge _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro input _
        by_cases hport : rule.network.edgePort edge input = rule.network.terminalVertex side <;>
          simp only [hport, ↓reduceIte, Finset.sum_const_zero, terminalPrefixCount]
      _ ≤ ∑ edge : Fin rule.edges, ∑ input : Bool,
          if rule.network.edgePort edge input = rule.network.terminalVertex side then
            (rule.network.fullGraph.degree rule.network.source) ^ n else 0 := by
        apply Finset.sum_le_sum
        intro edge _
        apply Finset.sum_le_sum
        intro input _
        split_ifs
        · exact ih input
        · exact le_rfl
      _ = (∑ edge : Fin rule.edges, ∑ input : Bool,
          if rule.network.edgePort edge input = rule.network.terminalVertex side then (1 : ℕ) else 0) *
            (rule.network.fullGraph.degree rule.network.source) ^ n := by
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro edge _
        apply Finset.sum_congr rfl
        intro input _
        split_ifs <;> simp
      _ = (rule.network.fullGraph.degree rule.network.source) ^ (n + 1) := by
        rw [h.terminal_port_row_sum, pow_succ']

end
end Universality.Rule
