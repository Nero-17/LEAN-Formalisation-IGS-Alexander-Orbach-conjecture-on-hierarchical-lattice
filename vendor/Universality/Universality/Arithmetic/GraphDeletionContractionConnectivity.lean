import Universality.Arithmetic.GraphCanonicalAugmentation

/-!
# Vertex connectivity under deletion and contraction

The graph with the endpoints of an edge removed is the vertex-deleted graph
at the contracted vertex. The dichotomy below proves this remaining condition
for contraction whenever deletion fails to preserve vertex connectivity.
-/

namespace Universality.Section4
noncomputable section
open SimpleGraph

variable {Vertex : Type*} {graph : SimpleGraph Vertex}

set_option backward.isDefEq.respectTransparency false in
theorem exists_path_avoiding_of_induce_preconnected (removed first second : Vertex)
    (hconnected : (graph.induce {vertex | vertex ≠ removed}).Preconnected)
    (hfirst : first ≠ removed) (hsecond : second ≠ removed) :
    ∃ path : graph.Walk first second, path.IsPath ∧ removed ∉ path.support := by
  obtain ⟨path, hpath⟩ := hconnected.exists_isPath ⟨first, hfirst⟩ ⟨second, hsecond⟩
  refine ⟨path.map (Embedding.induce _).toHom, hpath.map Subtype.val_injective, ?_⟩
  rw [SimpleGraph.Walk.support_map]
  rw [List.mem_map]
  rintro ⟨vertex, _, hequal⟩
  exact vertex.property hequal

theorem induce_delete_edge_eq_of_endpoint_not_mem (vertices : Set Vertex)
    (first second : Vertex) (hfirst : first ∉ vertices) :
    ((graph.deleteEdges {s(first, second)}).induce vertices) = graph.induce vertices := by
  ext vertex neighbor
  simp only [induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · exact And.left
  · intro hadj
    refine ⟨hadj, ?_⟩
    intro hequal
    rcases Sym2.eq_iff.mp hequal with hequal | hequal
    · exact hfirst (hequal.1 ▸ vertex.property)
    · exact hfirst (hequal.2 ▸ neighbor.property)

theorem induce_delete_edge_eq (vertices : Set Vertex) (first second : Vertex)
    (hfirst : first ∈ vertices) (hsecond : second ∈ vertices) :
    ((graph.deleteEdges {s(first, second)}).induce vertices) =
      (graph.induce vertices).deleteEdges {s(⟨first, hfirst⟩, ⟨second, hsecond⟩)} := by
  ext vertex neighbor
  simp only [induce_adj, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff,
    Subtype.ext_iff]

theorem reachable_endpoint_after_edge_deletion (hconnected : graph.Preconnected)
    (vertex first second : Vertex) (hdistinct : first ≠ second) :
    (graph.deleteEdges {s(first, second)}).Reachable vertex first ∨
      (graph.deleteEdges {s(first, second)}).Reachable vertex second := by
  classical
  obtain ⟨path, hpath⟩ := hconnected.exists_isPath vertex first
  by_cases hedge : s(first, second) ∈ path.edges
  · have hsecond := path.snd_mem_support_of_mem_edges hedge
    have hfirst := Walk.endpoint_notMem_support_takeUntil hpath hsecond hdistinct
    right
    exact ⟨(path.takeUntil second hsecond).toDeleteEdge _
      (fun hedge => hfirst ((path.takeUntil second hsecond).fst_mem_support_of_mem_edges hedge))⟩
  · exact Or.inl ⟨path.toDeleteEdge _ hedge⟩

/-- For an edge of a vertex-connected graph, deletion preserves all
vertex-deletion connectivity, or removal of the two endpoints is preconnected.
The latter is the condition at the contracted vertex in the contraction. -/
theorem delete_edge_vertex_connected_or_delete_endpoints_preconnected
    (hconnected : ∀ removed : Vertex,
      (graph.induce {vertex | vertex ≠ removed}).Preconnected)
    (first second : Vertex) :
    (∀ removed : Vertex,
      ((graph.deleteEdges {s(first, second)}).induce
        {vertex | vertex ≠ removed}).Preconnected) ∨
      (graph.induce {vertex | vertex ≠ first ∧ vertex ≠ second}).Preconnected := by
  classical
  by_cases hdelete : ∀ removed : Vertex,
      ((graph.deleteEdges {s(first, second)}).induce
        {vertex | vertex ≠ removed}).Preconnected
  · exact Or.inl hdelete
  right
  push Not at hdelete
  obtain ⟨removed, hdisconnected⟩ := hdelete
  have hfirst : first ≠ removed := by
    intro hequal
    subst first
    rw [induce_delete_edge_eq_of_endpoint_not_mem _ _ _ (by simp)] at hdisconnected
    exact hdisconnected (hconnected removed)
  have hsecond : second ≠ removed := by
    intro hequal
    subst second
    rw [Sym2.eq_swap, induce_delete_edge_eq_of_endpoint_not_mem _ _ _ (by simp)]
      at hdisconnected
    exact hdisconnected (hconnected removed)
  have hseparated : ¬ ((graph.deleteEdges {s(first, second)}).induce
      {vertex | vertex ≠ removed}).Reachable ⟨first, hfirst⟩ ⟨second, hsecond⟩ := by
    intro hreachable
    letI : Nonempty {vertex : Vertex | vertex ≠ removed} := ⟨⟨first, hfirst⟩⟩
    have hconnected' : (graph.induce {vertex | vertex ≠ removed}).Connected :=
      ⟨hconnected removed⟩
    have hreachable' := hreachable
    rw [induce_delete_edge_eq _ _ _ hfirst hsecond] at hreachable'
    have hpreserved := hconnected'.connected_delete_edge_of_not_isBridge
      (x := ⟨first, hfirst⟩) (y := ⟨second, hsecond⟩)
      (by simpa only [isBridge_iff, not_not] using hreachable')
    apply hdisconnected
    rw [induce_delete_edge_eq _ _ _ hfirst hsecond]
    exact hpreserved.preconnected
  have hdistinct : first ≠ second := by
    intro hequal
    subst second
    exact hseparated .rfl
  have hpaths : ∀ vertex : Vertex, vertex ≠ first → vertex ≠ second →
      ∃ path : graph.Walk vertex removed,
        first ∉ path.support ∧ second ∉ path.support := by
    intro vertex hvertexFirst hvertexSecond
    by_cases hvertex : vertex = removed
    · subst vertex
      exact ⟨.nil, by simpa using hfirst, by simpa using hsecond⟩
    have hsides := reachable_endpoint_after_edge_deletion (hconnected removed)
      ⟨vertex, hvertex⟩ ⟨first, hfirst⟩ ⟨second, hsecond⟩
      (fun hequal => hdistinct (congrArg Subtype.val hequal))
    rw [← induce_delete_edge_eq _ _ _ hfirst hsecond] at hsides
    rcases hsides with hreachFirst | hreachSecond
    · obtain ⟨path, hpath, havoidFirst⟩ :=
        exists_path_avoiding_of_induce_preconnected first vertex removed
          (hconnected first) hvertexFirst hfirst.symm
      refine ⟨path, havoidFirst, ?_⟩
      intro hcontainsSecond
      have havoidRemoved := Walk.endpoint_notMem_support_takeUntil hpath
        hcontainsSecond hsecond.symm
      have havoidFirstPrefix : first ∉ (path.takeUntil second hcontainsSecond).support :=
        fun hmember => havoidFirst (path.support_takeUntil_subset_support hcontainsSecond hmember)
      have hedge : s(first, second) ∉ (path.takeUntil second hcontainsSecond).edges :=
        fun hmember => havoidFirstPrefix
          ((path.takeUntil second hcontainsSecond).fst_mem_support_of_mem_edges hmember)
      have hreachSecond : ((graph.deleteEdges {s(first, second)}).induce
          {vertex | vertex ≠ removed}).Reachable ⟨vertex, hvertex⟩ ⟨second, hsecond⟩ := by
        refine ⟨((path.takeUntil second hcontainsSecond).toDeleteEdge _ hedge).induce _ ?_⟩
        intro neighbor hmember hequal
        apply havoidRemoved
        simpa only [Walk.support_transfer, hequal] using hmember
      exact hseparated (hreachFirst.symm.trans hreachSecond)
    · obtain ⟨path, hpath, havoidSecond⟩ :=
        exists_path_avoiding_of_induce_preconnected second vertex removed
          (hconnected second) hvertexSecond hsecond.symm
      refine ⟨path, ?_, havoidSecond⟩
      intro hcontainsFirst
      have havoidRemoved := Walk.endpoint_notMem_support_takeUntil hpath
        hcontainsFirst hfirst.symm
      have havoidSecondPrefix : second ∉ (path.takeUntil first hcontainsFirst).support :=
        fun hmember => havoidSecond (path.support_takeUntil_subset_support hcontainsFirst hmember)
      have hedge : s(first, second) ∉ (path.takeUntil first hcontainsFirst).edges :=
        fun hmember => havoidSecondPrefix
          ((path.takeUntil first hcontainsFirst).snd_mem_support_of_mem_edges hmember)
      have hreachFirst : ((graph.deleteEdges {s(first, second)}).induce
          {vertex | vertex ≠ removed}).Reachable ⟨vertex, hvertex⟩ ⟨first, hfirst⟩ := by
        refine ⟨((path.takeUntil first hcontainsFirst).toDeleteEdge _ hedge).induce _ ?_⟩
        intro neighbor hmember hequal
        apply havoidRemoved
        simpa only [Walk.support_transfer, hequal] using hmember
      exact hseparated (hreachFirst.symm.trans hreachSecond)
  intro vertex neighbor
  obtain ⟨firstPath, hfirstPath⟩ := hpaths vertex.val vertex.property.1 vertex.property.2
  obtain ⟨secondPath, hsecondPath⟩ := hpaths neighbor.val neighbor.property.1 neighbor.property.2
  refine ⟨(firstPath.append secondPath.reverse).induce _ ?_⟩
  intro other hmember
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hmember
  rcases hmember with hmember | hmember
  · exact ⟨fun hequal => hfirstPath.1 (hequal ▸ hmember),
      fun hequal => hfirstPath.2 (hequal ▸ hmember)⟩
  · exact ⟨fun hequal => hsecondPath.1 (hequal ▸ hmember),
      fun hequal => hsecondPath.2 (hequal ▸ hmember)⟩

end
end Universality.Section4

#print axioms Universality.Section4.delete_edge_vertex_connected_or_delete_endpoints_preconnected
