import Universality.Arithmetic.GraphDeletionContractionConnectivity

/-! An edge has an alternate path when vertex deletion preserves connectivity
and there is a third vertex. No finiteness or edge-adjacency premise is needed. -/

namespace Universality.Section4
noncomputable section
open SimpleGraph

variable {Vertex : Type*} {graph : SimpleGraph Vertex}

theorem reachable_after_edge_deletion_of_vertex_preconnected
    (hconnected : ∀ removed : Vertex,
      (graph.induce {vertex | vertex ≠ removed}).Preconnected)
    (first second third : Vertex) (hfirst : third ≠ first) (hsecond : third ≠ second) :
    (graph.deleteEdges {s(first, second)}).Reachable first second := by
  classical
  by_cases hequal : first = second
  · subst second
    exact .rfl
  obtain ⟨firstPath, _, hfirstPath⟩ :=
    exists_path_avoiding_of_induce_preconnected second first third
      (hconnected second) hequal hsecond
  obtain ⟨secondPath, _, hsecondPath⟩ :=
    exists_path_avoiding_of_induce_preconnected first third second
      (hconnected first) hfirst (Ne.symm hequal)
  have hfirstEdge : s(first, second) ∉ firstPath.edges := by
    intro hmember
    exact hfirstPath (firstPath.snd_mem_support_of_mem_edges hmember)
  have hsecondEdge : s(first, second) ∉ secondPath.edges := by
    intro hmember
    exact hsecondPath (secondPath.fst_mem_support_of_mem_edges hmember)
  exact ⟨(firstPath.toDeleteEdge _ hfirstEdge).append
    (secondPath.toDeleteEdge _ hsecondEdge)⟩

end
end Universality.Section4

#print axioms Universality.Section4.reachable_after_edge_deletion_of_vertex_preconnected
