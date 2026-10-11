import Universality.Graph.ClassicalRule

/-!
# Canonical terminal paths and the graph with an added terminal edge

These are graph prerequisites for the standalone full-degree problem. They do
not assert nonvanishing of the alternating configuration sum or introduce a
beta-invariant positivity theorem as an assumption.
-/

namespace Universality.FiniteNetwork

variable {vertices edges : ℕ}

def terminalAugmentedGraph (network : FiniteNetwork vertices edges) : SimpleGraph (Fin vertices) :=
  network.fullGraph ⊔ SimpleGraph.edge network.source network.target

theorem fullGraph_le_terminalAugmentedGraph (network : FiniteNetwork vertices edges) :
    network.fullGraph ≤ network.terminalAugmentedGraph := le_sup_left

theorem terminalAugmentedGraph_terminals_adjacent (network : FiniteNetwork vertices edges) :
    network.terminalAugmentedGraph.Adj network.source network.target := by
  right
  exact (SimpleGraph.edge_adj network.source network.target network.source network.target).mpr
    ⟨Or.inl ⟨rfl, rfl⟩, network.terminals_distinct⟩

end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- Every original edge belongs to a simple cycle containing the new terminal
edge. This is the graph statement behind connectivity of the cycle matroid. -/
theorem Classical.augmented_cycle_through_edge {rule : Rule} (h : rule.Classical)
    (edge : Fin rule.edges) :
    ∃ cycle : rule.network.terminalAugmentedGraph.Walk rule.network.source rule.network.source,
      cycle.IsCycle ∧
      s(rule.network.source, rule.network.target) ∈ cycle.edges ∧
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) ∈ cycle.edges := by
  obtain ⟨path, hpath, hedge⟩ := h.canonical edge
  have hnotAdjacent : ¬ rule.network.fullGraph.Adj rule.network.source rule.network.target := by
    intro hadj
    have hdistance := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have hscale := h.scale
    omega
  refine ⟨.cons rule.network.terminalAugmentedGraph_terminals_adjacent
    (path.reverse.mapLe rule.network.fullGraph_le_terminalAugmentedGraph), ?_, ?_, ?_⟩
  · apply (SimpleGraph.Walk.cons_isCycle_iff _ _).mpr
    refine ⟨hpath.reverse.mapLe _, ?_⟩
    simp only [SimpleGraph.Walk.edges_mapLe_eq_edges, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse]
    intro hmember
    exact hnotAdjacent (path.edges_subset_edgeSet hmember)
  · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, true_or]
  · simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_mapLe_eq_edges,
      SimpleGraph.Walk.edges_reverse, List.mem_cons, List.mem_reverse]
    exact Or.inr hedge

/-- Connectedness and canonicality put every vertex on a simple terminal path. -/
theorem Classical.vertex_on_terminal_path {rule : Rule} (h : rule.Classical)
    (vertex : Fin rule.vertices) :
    ∃ path : rule.network.fullGraph.Walk rule.network.source rule.network.target,
      path.IsPath ∧ vertex ∈ path.support := by
  by_cases hsource : vertex = rule.network.source
  · subst vertex
    obtain ⟨path, hpath⟩ := (h.connected rule.network.target).exists_isPath
    exact ⟨path, hpath, path.start_mem_support⟩
  obtain ⟨walk⟩ := (h.connected vertex).symm
  have hadj := walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne hsource)
  obtain ⟨_, edge, _, hpair⟩ := hadj
  obtain ⟨path, hpath, hedge⟩ := h.canonical edge
  refine ⟨path, hpath, ?_⟩
  rcases hpair with hpair | hpair
  · have hmember := path.fst_mem_support_of_mem_edges hedge
    simpa only [hpair] using hmember
  · have hmember := path.snd_mem_support_of_mem_edges hedge
    simpa only [hpair] using hmember

/-- A simple terminal path through a surviving vertex reaches at least one
terminal without visiting an arbitrary removed vertex. -/
theorem Classical.vertex_reaches_terminal_avoiding {rule : Rule} (h : rule.Classical)
    (removed vertex : Fin rule.vertices) (hne : vertex ≠ removed) :
    ∃ terminal, (terminal = rule.network.source ∨ terminal = rule.network.target) ∧
      ∃ walk : rule.network.fullGraph.Walk vertex terminal, removed ∉ walk.support := by
  obtain ⟨path, hpath, hvertex⟩ := h.vertex_on_terminal_path vertex
  obtain ⟨first, second, _, _, hsplit⟩ := hpath.mem_support_iff_exists_append.mp hvertex
  have hsplitPath : (first.append second).IsPath := hsplit ▸ hpath
  by_cases hfirst : removed ∈ first.support
  · refine ⟨rule.network.target, Or.inr rfl, second, ?_⟩
    intro hsecond
    exact (hsplitPath.ne_of_mem_support_of_append hne.symm hfirst hsecond) rfl
  · exact ⟨rule.network.source, Or.inl rfl, first.reverse,
      by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hfirst⟩

/-- Adding the terminal edge allows any two surviving vertices to be connected
while avoiding the removed vertex. -/
theorem Classical.augmented_walk_avoiding_vertex {rule : Rule} (h : rule.Classical)
    (removed first second : Fin rule.vertices) (hfirst : first ≠ removed) (hsecond : second ≠ removed) :
    ∃ walk : rule.network.terminalAugmentedGraph.Walk first second, removed ∉ walk.support := by
  obtain ⟨firstTerminal, hfirstTerminal, firstWalk, hfirstWalk⟩ :=
    h.vertex_reaches_terminal_avoiding removed first hfirst
  obtain ⟨secondTerminal, hsecondTerminal, secondWalk, hsecondWalk⟩ :=
    h.vertex_reaches_terminal_avoiding removed second hsecond
  have hfirstTerminalNe : removed ≠ firstTerminal := by
    intro hequal
    exact hfirstWalk (hequal ▸ firstWalk.end_mem_support)
  have hsecondTerminalNe : removed ≠ secondTerminal := by
    intro hequal
    exact hsecondWalk (hequal ▸ secondWalk.end_mem_support)
  have hbridge : ∃ bridge : rule.network.terminalAugmentedGraph.Walk firstTerminal secondTerminal,
      removed ∉ bridge.support := by
    rcases hfirstTerminal with hsource | htarget <;> subst firstTerminal
    · rcases hsecondTerminal with hsource | htarget <;> subst secondTerminal
      · exact ⟨.nil, by simpa using hfirstTerminalNe⟩
      · exact ⟨.cons rule.network.terminalAugmentedGraph_terminals_adjacent .nil,
          by simpa using ⟨hfirstTerminalNe, hsecondTerminalNe⟩⟩
    · rcases hsecondTerminal with hsource | htarget <;> subst secondTerminal
      · exact ⟨.cons rule.network.terminalAugmentedGraph_terminals_adjacent.symm .nil,
          by simpa using ⟨hfirstTerminalNe, hsecondTerminalNe⟩⟩
      · exact ⟨.nil, by simpa using hfirstTerminalNe⟩
  obtain ⟨bridge, hbridge⟩ := hbridge
  refine ⟨(firstWalk.mapLe rule.network.fullGraph_le_terminalAugmentedGraph).append
    (bridge.append (secondWalk.reverse.mapLe rule.network.fullGraph_le_terminalAugmentedGraph)), ?_⟩
  simp only [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_mapLe_eq_support, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact not_or.mpr ⟨hfirstWalk, not_or.mpr ⟨hbridge, hsecondWalk⟩⟩

/-- Deletion of any vertex from the augmented graph leaves a preconnected
graph, an explicit vertex-connectivity consequence of canonicality. -/
theorem Classical.terminalAugmentedGraph_preconnected_delete_vertex {rule : Rule}
    (h : rule.Classical) (removed : Fin rule.vertices) :
    (rule.network.terminalAugmentedGraph.induce {vertex | vertex ≠ removed}).Preconnected := by
  intro first second
  obtain ⟨walk, hwalk⟩ := h.augmented_walk_avoiding_vertex removed first.val second.val
    first.property second.property
  have hsupport : ∀ vertex ∈ walk.support, vertex ∈ {vertex | vertex ≠ removed} := by
    intro vertex hvertex hequal
    exact hwalk (hequal ▸ hvertex)
  exact ⟨walk.induce _ hsupport⟩

end
end Universality.Rule

#print axioms Universality.Rule.Classical.augmented_cycle_through_edge
#print axioms Universality.Rule.Classical.terminalAugmentedGraph_preconnected_delete_vertex
