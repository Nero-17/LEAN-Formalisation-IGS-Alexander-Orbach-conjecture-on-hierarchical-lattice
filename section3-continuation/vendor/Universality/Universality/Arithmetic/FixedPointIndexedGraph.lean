import Universality.Arithmetic.FixedPointActiveVertices

/-! Graph and looplessness bridges for indexed deletion–contraction. -/

namespace Universality.Section4.IndexedNetwork

noncomputable section
variable {V : Type*} {edges : ℕ}

def openGraph (network : IndexedNetwork V edges) (configuration : Fin edges → Bool) :
    SimpleGraph V where
  Adj first second := first ≠ second ∧ ∃ edge, configuration edge = true ∧
    (network.endpoint edge = (first, second) ∨ network.endpoint edge = (second, first))
  symm := ⟨by
    intro first second h
    rcases h with ⟨hdistinct, edge, hopen, hedge | hedge⟩
    · exact ⟨hdistinct.symm, edge, hopen, Or.inr hedge⟩
    · exact ⟨hdistinct.symm, edge, hopen, Or.inl hedge⟩⟩
  loopless := ⟨by intro vertex h; exact h.1 rfl⟩

def fullGraph (network : IndexedNetwork V edges) : SimpleGraph V :=
  network.openGraph (fun _ => true)

def augmentedGraph (network : IndexedNetwork V edges) : SimpleGraph V :=
  network.fullGraph ⊔ SimpleGraph.edge network.source network.target

def activeAugmentedGraph (network : IndexedNetwork V edges) (vertices : Finset V) :
    SimpleGraph {vertex // vertex ∈ vertices} :=
  network.augmentedGraph.induce (↑vertices : Set V)

theorem linked_iff_reachable (network : IndexedNetwork V edges)
    (configuration : Fin edges → Bool) (first second : V) :
    network.Linked configuration first second ↔
      (network.openGraph configuration).Reachable first second := by
  constructor
  · intro h
    induction h with
    | rel first second h =>
        obtain ⟨edge, hopen, hedge⟩ := h
        by_cases hequal : first = second
        · subst second
          exact .refl _
        · exact (show (network.openGraph configuration).Adj first second from
            ⟨hequal, edge, hopen, Or.inl hedge⟩).reachable
    | refl => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihfirst ihsecond => exact ihfirst.trans ihsecond
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact Relation.EqvGen.refl _
    | @cons first middle last hadj walk ih =>
        obtain ⟨_, edge, hopen, hedge | hedge⟩ := hadj
        · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨edge, hopen, hedge⟩) ih
        · exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨edge, hopen, hedge⟩)) ih

theorem fullGraph_adj_iff (network : IndexedNetwork V edges) (first second : V) :
    network.fullGraph.Adj first second ↔ first ≠ second ∧
      ∃ edge, network.endpoint edge = (first, second) ∨ network.endpoint edge = (second, first) := by
  simp only [fullGraph, openGraph, true_and]

theorem fullGraph_deleteHead_le (network : IndexedNetwork V (edges + 1)) :
    network.deleteHead.fullGraph ≤ network.fullGraph := by
  intro first second hadj
  obtain ⟨hdistinct, edge, hedge⟩ := (network.deleteHead.fullGraph_adj_iff first second).mp hadj
  exact (network.fullGraph_adj_iff first second).mpr ⟨hdistinct, edge.succ, hedge⟩

theorem fullGraph_head_adjacent (network : IndexedNetwork V (edges + 1))
    (hdistinct : (network.endpoint 0).1 ≠ (network.endpoint 0).2) :
    network.fullGraph.Adj (network.endpoint 0).1 (network.endpoint 0).2 := by
  exact (network.fullGraph_adj_iff _ _).mpr ⟨hdistinct, 0, Or.inl (Prod.eta _)⟩

theorem merge_eq_merge_iff [DecidableEq V] (removed destination first second : V) :
    merge removed destination first = merge removed destination second ↔
      first = second ∨ (first = removed ∧ second = destination) ∨
        (first = destination ∧ second = removed) := by
  by_cases hfirst : first = removed <;> by_cases hsecond : second = removed <;>
    simp_all [merge, eq_comm]

theorem contractHead_loopless [DecidableEq V] (network : IndexedNetwork V (edges + 1))
    (hloopless : ∀ edge, (network.endpoint edge).1 ≠ (network.endpoint edge).2)
    (hnonparallel : ∀ edge : Fin edges,
      network.endpoint edge.succ ≠ network.endpoint 0 ∧
      network.endpoint edge.succ ≠ ((network.endpoint 0).2, (network.endpoint 0).1)) :
    ∀ edge, (network.contractHead.endpoint edge).1 ≠ (network.contractHead.endpoint edge).2 := by
  intro edge hequal
  change merge _ _ _ = merge _ _ _ at hequal
  rcases (merge_eq_merge_iff _ _ _ _).mp hequal with hequal | hequal | hequal
  · exact hloopless edge.succ hequal
  · exact (hnonparallel edge).1 (Prod.ext hequal.1 hequal.2)
  · exact (hnonparallel edge).2 (Prod.ext hequal.1 hequal.2)

theorem contractHead_terminals_distinct [DecidableEq V] (network : IndexedNetwork V (edges + 1))
    (hdistinct : network.source ≠ network.target)
    (hnondirect : network.endpoint 0 ≠ (network.source, network.target) ∧
      network.endpoint 0 ≠ (network.target, network.source)) :
    network.contractHead.source ≠ network.contractHead.target := by
  intro hequal
  change merge _ _ _ = merge _ _ _ at hequal
  rcases (merge_eq_merge_iff _ _ _ _).mp hequal with hequal | hequal | hequal
  · exact hdistinct hequal
  · exact hnondirect.1 (Prod.ext hequal.1.symm hequal.2.symm)
  · exact hnondirect.2 (Prod.ext hequal.2.symm hequal.1.symm)

theorem fullGraph_eq_deleteHead_sup_edge (network : IndexedNetwork V (edges + 1)) :
    network.fullGraph = network.deleteHead.fullGraph ⊔
      SimpleGraph.edge (network.endpoint 0).1 (network.endpoint 0).2 := by
  ext first second
  constructor
  · intro hadj
    obtain ⟨hdistinct, edge, hedge⟩ := (network.fullGraph_adj_iff first second).mp hadj
    revert hedge
    refine Fin.cases ?_ (fun edge hedge => ?_) edge
    · intro hedge
      right
      rcases hedge with hedge | hedge
      · rw [hedge]
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hdistinct⟩
      · rw [hedge]
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl, rfl⟩, hdistinct⟩
    · left
      exact (network.deleteHead.fullGraph_adj_iff first second).mpr ⟨hdistinct, edge, hedge⟩
  · rintro (hadj | hadj)
    · exact network.fullGraph_deleteHead_le hadj
    · rcases (SimpleGraph.edge_adj _ _ _ _).mp hadj with ⟨hequal, hdistinct⟩
      rcases hequal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact network.fullGraph_head_adjacent hdistinct
      · exact (network.fullGraph_head_adjacent hdistinct.symm).symm

theorem fullGraph_deleteHead_eq_of_parallel (network : IndexedNetwork V (edges + 1))
    (hparallel : ∃ edge : Fin edges, network.endpoint edge.succ = network.endpoint 0 ∨
      network.endpoint edge.succ = ((network.endpoint 0).2, (network.endpoint 0).1)) :
    network.deleteHead.fullGraph = network.fullGraph := by
  obtain ⟨edge, hedge⟩ := hparallel
  rw [network.fullGraph_eq_deleteHead_sup_edge]
  apply (sup_eq_left.mpr ?_).symm
  intro first second hadj
  rcases (SimpleGraph.edge_adj _ _ _ _).mp hadj with ⟨hequal, hdistinct⟩
  apply (network.deleteHead.fullGraph_adj_iff first second).mpr
  refine ⟨hdistinct, edge, ?_⟩
  change network.endpoint edge.succ = (first, second) ∨ network.endpoint edge.succ = (second, first)
  rcases hequal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hedge with hedge | hedge
    · exact Or.inl (hedge.trans (Prod.eta _))
    · exact Or.inr hedge
  · rcases hedge with hedge | hedge
    · exact Or.inr (hedge.trans (Prod.eta _))
    · exact Or.inl hedge

theorem augmentedGraph_deleteHead_eq_of_parallel (network : IndexedNetwork V (edges + 1))
    (hparallel : ∃ edge : Fin edges, network.endpoint edge.succ = network.endpoint 0 ∨
      network.endpoint edge.succ = ((network.endpoint 0).2, (network.endpoint 0).1)) :
    network.deleteHead.augmentedGraph = network.augmentedGraph := by
  unfold augmentedGraph
  rw [network.fullGraph_deleteHead_eq_of_parallel hparallel]
  rfl

theorem augmentedGraph_deleteHead_eq_of_direct (network : IndexedNetwork V (edges + 1))
    (hdirect : network.endpoint 0 = (network.source, network.target) ∨
      network.endpoint 0 = (network.target, network.source)) :
    network.deleteHead.augmentedGraph = network.augmentedGraph := by
  unfold augmentedGraph
  rw [network.fullGraph_eq_deleteHead_sup_edge]
  change network.deleteHead.fullGraph ⊔ SimpleGraph.edge network.source network.target = _
  rcases hdirect with hdirect | hdirect
  · rw [hdirect]
    simp only [sup_assoc, sup_idem]
  · rw [hdirect]
    rw [SimpleGraph.edge_comm]
    simp only [sup_assoc, sup_idem]
theorem fullGraph_merge_adj [DecidableEq V] (network : IndexedNetwork V (edges + 1))
    {first second : V} (hadj : network.fullGraph.Adj first second)
    (hdistinct : merge (network.endpoint 0).1 (network.endpoint 0).2 first ≠
      merge (network.endpoint 0).1 (network.endpoint 0).2 second) :
    network.contractHead.fullGraph.Adj
      (merge (network.endpoint 0).1 (network.endpoint 0).2 first)
      (merge (network.endpoint 0).1 (network.endpoint 0).2 second) := by
  obtain ⟨_, edge, hedge⟩ := (network.fullGraph_adj_iff first second).mp hadj
  revert hedge
  refine Fin.cases ?_ (fun edge hedge => ?_) edge
  · intro hedge
    exfalso
    apply hdistinct
    rcases hedge with hedge | hedge
    · have hfirst := congrArg Prod.fst hedge
      have hsecond := congrArg Prod.snd hedge
      simp only at hfirst hsecond
      rw [← hfirst, ← hsecond, merge_first, merge_second]
    · have hfirst := congrArg Prod.fst hedge
      have hsecond := congrArg Prod.snd hedge
      simp only at hfirst hsecond
      rw [← hfirst, ← hsecond, merge_first, merge_second]
  · apply (network.contractHead.fullGraph_adj_iff _ _).mpr
    refine ⟨hdistinct, edge, ?_⟩
    change (_, _) = (_, _) ∨ (_, _) = (_, _)
    rcases hedge with hedge | hedge
    · left
      rw [hedge]
    · right
      rw [hedge]

theorem augmentedGraph_merge_adj [DecidableEq V] (network : IndexedNetwork V (edges + 1))
    {first second : V} (hadj : network.augmentedGraph.Adj first second)
    (hdistinct : merge (network.endpoint 0).1 (network.endpoint 0).2 first ≠
      merge (network.endpoint 0).1 (network.endpoint 0).2 second) :
    network.contractHead.augmentedGraph.Adj
      (merge (network.endpoint 0).1 (network.endpoint 0).2 first)
      (merge (network.endpoint 0).1 (network.endpoint 0).2 second) := by
  rcases hadj with hadj | hadj
  · exact Or.inl (network.fullGraph_merge_adj hadj hdistinct)
  · right
    rcases (SimpleGraph.edge_adj _ _ _ _).mp hadj with ⟨hequal, _⟩
    rcases hequal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hdistinct⟩
    · exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl, rfl⟩, hdistinct⟩

theorem augmentedGraph_deleteEdges_head_le (network : IndexedNetwork V (edges + 1)) :
    network.augmentedGraph.deleteEdges {s((network.endpoint 0).1, (network.endpoint 0).2)} ≤
      network.deleteHead.augmentedGraph := by
  intro first second hadj
  obtain ⟨hadj, hnotedge⟩ := SimpleGraph.deleteEdges_adj.mp hadj
  rcases hadj with hadj | hadj
  · obtain ⟨hdistinct, edge, hedge⟩ := (network.fullGraph_adj_iff first second).mp hadj
    revert hedge
    refine Fin.cases ?_ (fun edge hedge => ?_) edge
    · intro hedge
      exfalso
      apply hnotedge
      rcases hedge with hedge | hedge <;> rw [hedge] <;> simp [Sym2.eq_swap]
    · left
      exact (network.deleteHead.fullGraph_adj_iff first second).mpr ⟨hdistinct, edge, hedge⟩
  · exact Or.inr hadj
end
end Universality.Section4.IndexedNetwork

#print axioms Universality.Section4.IndexedNetwork.linked_iff_reachable
#print axioms Universality.Section4.IndexedNetwork.contractHead_loopless


