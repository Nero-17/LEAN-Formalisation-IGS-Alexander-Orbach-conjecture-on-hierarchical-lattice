import Universality.Arithmetic.GraphDeletionContractionConnectivity
import Universality.Arithmetic.FixedPointIndexedGraph

/-! Vertex connectivity on the active vertices of an indexed network. -/

namespace Universality.Section4
noncomputable section
open SimpleGraph

theorem preconnected_of_surjective_weak_map {Vertex Target : Type*}
    {graph : SimpleGraph Vertex} {imageGraph : SimpleGraph Target}
    (function : Vertex → Target) (hsurjective : Function.Surjective function)
    (hadjacency : ∀ {first second}, graph.Adj first second →
      function first = function second ∨ imageGraph.Adj (function first) (function second))
    (hconnected : graph.Preconnected) : imageGraph.Preconnected := by
  intro first second
  obtain ⟨originalFirst, rfl⟩ := hsurjective first
  obtain ⟨originalSecond, rfl⟩ := hsurjective second
  obtain ⟨walk⟩ := hconnected originalFirst originalSecond
  induction walk with
  | nil => exact .rfl
  | @cons first middle last hadj walk ih =>
      rcases hadjacency hadj with hequal | hadj
      · simpa only [hequal] using ih
      · exact hadj.reachable.trans ih

theorem preconnected_induce_of_surjective_weak_map {Vertex Target : Type*}
    {graph : SimpleGraph Vertex} {imageGraph : SimpleGraph Target}
    (function : Vertex → Target) (vertices : Set Vertex) (imageVertices : Set Target)
    (hmaps : ∀ vertex ∈ vertices, function vertex ∈ imageVertices)
    (hsurjective : ∀ vertex ∈ imageVertices, ∃ original ∈ vertices, function original = vertex)
    (hadjacency : ∀ {first second}, graph.Adj first second →
      function first = function second ∨ imageGraph.Adj (function first) (function second))
    (hconnected : (graph.induce vertices).Preconnected) :
    (imageGraph.induce imageVertices).Preconnected := by
  apply preconnected_of_surjective_weak_map
    (graph := graph.induce vertices) (imageGraph := imageGraph.induce imageVertices)
    (fun vertex : vertices => (⟨function vertex, hmaps vertex vertex.property⟩ : imageVertices))
  · intro vertex
    obtain ⟨original, hmember, hequal⟩ := hsurjective vertex vertex.property
    exact ⟨⟨original, hmember⟩, Subtype.ext hequal⟩
  · intro first second hadj
    rcases hadjacency hadj with hequal | hadj
    · exact Or.inl (Subtype.ext hequal)
    · exact Or.inr hadj
  · exact hconnected

variable {Vertex : Type*} [DecidableEq Vertex] {graph : SimpleGraph Vertex}

theorem preconnected_active_erase_iff (vertices : Finset Vertex)
    (removed : {vertex // vertex ∈ vertices}) :
    ((graph.induce (↑vertices : Set Vertex)).induce {vertex | vertex ≠ removed}).Preconnected ↔
      (graph.induce (↑(vertices.erase removed.val) : Set Vertex)).Preconnected := by
  let equivalence :
      {vertex : {vertex // vertex ∈ vertices} // vertex ≠ removed} ≃
      {vertex // vertex ∈ vertices.erase removed.val} :=
    { toFun := fun vertex => ⟨vertex.val.val, Finset.mem_erase.mpr
        ⟨fun hequal => vertex.property (Subtype.ext hequal), vertex.val.property⟩⟩
      invFun := fun vertex => ⟨⟨vertex.val, (Finset.mem_erase.mp vertex.property).2⟩,
        fun hequal => (Finset.mem_erase.mp vertex.property).1 (congrArg Subtype.val hequal)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (show ((graph.induce (↑vertices : Set Vertex)).induce {vertex | vertex ≠ removed}) ≃g
      (graph.induce (↑(vertices.erase removed.val) : Set Vertex)) from
    { toEquiv := equivalence, map_rel_iff' := Iff.rfl }).preconnected_iff

theorem preconnected_active_erase_two_iff (vertices : Finset Vertex)
    (first second : {vertex // vertex ∈ vertices}) :
    ((graph.induce (↑vertices : Set Vertex)).induce
      {vertex | vertex ≠ first ∧ vertex ≠ second}).Preconnected ↔
      (graph.induce (↑((vertices.erase first.val).erase second.val) : Set Vertex)).Preconnected := by
  let equivalence :
      {vertex : {vertex // vertex ∈ vertices} // vertex ≠ first ∧ vertex ≠ second} ≃
      {vertex // vertex ∈ (vertices.erase first.val).erase second.val} :=
    { toFun := fun vertex => ⟨vertex.val.val, Finset.mem_erase.mpr
        ⟨fun hequal => vertex.property.2 (Subtype.ext hequal), Finset.mem_erase.mpr
          ⟨fun hequal => vertex.property.1 (Subtype.ext hequal), vertex.val.property⟩⟩⟩
      invFun := fun vertex => ⟨⟨vertex.val,
        (Finset.mem_erase.mp (Finset.mem_erase.mp vertex.property).2).2⟩,
        ⟨fun hequal => (Finset.mem_erase.mp (Finset.mem_erase.mp vertex.property).2).1
          (congrArg Subtype.val hequal),
         fun hequal => (Finset.mem_erase.mp vertex.property).1 (congrArg Subtype.val hequal)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (show ((graph.induce (↑vertices : Set Vertex)).induce
      {vertex | vertex ≠ first ∧ vertex ≠ second}) ≃g
      (graph.induce (↑((vertices.erase first.val).erase second.val) : Set Vertex)) from
    { toEquiv := equivalence, map_rel_iff' := Iff.rfl }).preconnected_iff

namespace IndexedNetwork
variable {edges : ℕ}

def VertexConnectedOn (network : IndexedNetwork Vertex edges) (vertices : Finset Vertex) : Prop :=
  ∀ removed ∈ vertices,
    (network.augmentedGraph.induce (↑(vertices.erase removed) : Set Vertex)).Preconnected

theorem vertexConnectedOn_iff_active (network : IndexedNetwork Vertex edges)
    (vertices : Finset Vertex) :
    network.VertexConnectedOn vertices ↔ ∀ removed : {vertex // vertex ∈ vertices},
      ((network.activeAugmentedGraph vertices).induce {vertex | vertex ≠ removed}).Preconnected := by
  constructor
  · intro h removed
    exact (preconnected_active_erase_iff vertices removed).mpr (h removed removed.property)
  · intro h removed hremoved
    exact (preconnected_active_erase_iff vertices ⟨removed, hremoved⟩).mp (h ⟨removed, hremoved⟩)

theorem VertexConnectedOn.contractHead_of_endpoints
    {network : IndexedNetwork Vertex (edges + 1)} {vertices : Finset Vertex}
    (hconnected : network.VertexConnectedOn vertices)
    (hsupport : network.SupportedOn vertices)
    (hdistinct : (network.endpoint 0).1 ≠ (network.endpoint 0).2)
    (hendpoints : (network.augmentedGraph.induce
      (↑((vertices.erase (network.endpoint 0).1).erase (network.endpoint 0).2) : Set Vertex)).Preconnected) :
    network.contractHead.VertexConnectedOn (vertices.erase (network.endpoint 0).1) := by
  have hmap : ∀ {first second}, network.augmentedGraph.Adj first second →
      merge (network.endpoint 0).1 (network.endpoint 0).2 first =
          merge (network.endpoint 0).1 (network.endpoint 0).2 second ∨
        network.contractHead.augmentedGraph.Adj
          (merge (network.endpoint 0).1 (network.endpoint 0).2 first)
          (merge (network.endpoint 0).1 (network.endpoint 0).2 second) := by
    intro first second hadj
    by_cases hequal : merge (network.endpoint 0).1 (network.endpoint 0).2 first =
        merge (network.endpoint 0).1 (network.endpoint 0).2 second
    · exact Or.inl hequal
    · exact Or.inr (network.augmentedGraph_merge_adj hadj hequal)
  intro removed hremoved
  by_cases hequal : removed = (network.endpoint 0).2
  · subst removed
    apply preconnected_induce_of_surjective_weak_map
      (merge (network.endpoint 0).1 (network.endpoint 0).2)
      (↑((vertices.erase (network.endpoint 0).1).erase (network.endpoint 0).2) : Set Vertex)
      (↑((vertices.erase (network.endpoint 0).1).erase (network.endpoint 0).2) : Set Vertex)
      _ _ hmap hendpoints
    · intro vertex hvertex
      have hne := (Finset.mem_erase.mp (Finset.mem_erase.mp hvertex).2).1
      simpa only [merge, if_neg hne] using hvertex
    · intro vertex hvertex
      refine ⟨vertex, hvertex, ?_⟩
      exact if_neg (Finset.mem_erase.mp (Finset.mem_erase.mp hvertex).2).1
  · apply preconnected_induce_of_surjective_weak_map
      (merge (network.endpoint 0).1 (network.endpoint 0).2)
      (↑(vertices.erase removed) : Set Vertex)
      (↑((vertices.erase (network.endpoint 0).1).erase removed) : Set Vertex)
      _ _ hmap (hconnected removed (Finset.mem_erase.mp hremoved).2)
    · intro vertex hvertex
      obtain ⟨hne, hmember⟩ := Finset.mem_erase.mp hvertex
      refine Finset.mem_erase.mpr ⟨?_, merge_mem_erase (hsupport.2.2 0).2 hdistinct hmember⟩
      by_cases hfirst : vertex = (network.endpoint 0).1
      · simpa only [hfirst, merge_first] using (Ne.symm hequal)
      · simpa only [merge, if_neg hfirst] using hne
    · intro vertex hvertex
      obtain ⟨hne, hmember⟩ := Finset.mem_erase.mp hvertex
      obtain ⟨hfirst, hmember⟩ := Finset.mem_erase.mp hmember
      exact ⟨vertex, Finset.mem_erase.mpr ⟨hne, hmember⟩, if_neg hfirst⟩

set_option backward.isDefEq.respectTransparency false in
/-- One actual indexed minor retains vertex connectivity on its active set.
Parallel edges and the virtual terminal edge are retained by the deletion
branch; this statement does not silently discard any indexed Bernoulli edge. -/
theorem VertexConnectedOn.delete_or_contract
    {network : IndexedNetwork Vertex (edges + 1)} {vertices : Finset Vertex}
    (hconnected : network.VertexConnectedOn vertices)
    (hsupport : network.SupportedOn vertices)
    (hdistinct : (network.endpoint 0).1 ≠ (network.endpoint 0).2) :
    network.deleteHead.VertexConnectedOn vertices ∨
      network.contractHead.VertexConnectedOn (vertices.erase (network.endpoint 0).1) := by
  have hdichotomy := delete_edge_vertex_connected_or_delete_endpoints_preconnected
    ((network.vertexConnectedOn_iff_active vertices).mp hconnected)
    ⟨(network.endpoint 0).1, (hsupport.2.2 0).1⟩
    ⟨(network.endpoint 0).2, (hsupport.2.2 0).2⟩
  rcases hdichotomy with hdelete | hcontract
  · left
    apply (network.deleteHead.vertexConnectedOn_iff_active vertices).mpr
    intro removed
    apply (hdelete removed).mono
    have hle : (network.activeAugmentedGraph vertices).deleteEdges
        {s(⟨(network.endpoint 0).1, (hsupport.2.2 0).1⟩,
          ⟨(network.endpoint 0).2, (hsupport.2.2 0).2⟩)} ≤
        network.deleteHead.activeAugmentedGraph vertices := by
      intro first second hadj
      apply network.augmentedGraph_deleteEdges_head_le
      obtain ⟨hadj, hnotedge⟩ := SimpleGraph.deleteEdges_adj.mp hadj
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩
      intro hequal
      apply hnotedge
      simp only [Set.mem_singleton_iff] at hequal ⊢
      rcases Sym2.eq_iff.mp hequal with hequal | hequal
      · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hequal.1, Subtype.ext hequal.2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hequal.1, Subtype.ext hequal.2⟩)
    intro first second hadj
    exact hle hadj
  · right
    apply hconnected.contractHead_of_endpoints hsupport hdistinct
    exact (preconnected_active_erase_two_iff vertices
      ⟨(network.endpoint 0).1, (hsupport.2.2 0).1⟩
      ⟨(network.endpoint 0).2, (hsupport.2.2 0).2⟩).mp hcontract

theorem VertexConnectedOn.deleteHead_of_parallel
    {network : IndexedNetwork Vertex (edges + 1)} {vertices : Finset Vertex}
    (hconnected : network.VertexConnectedOn vertices)
    (hparallel : ∃ edge : Fin edges, network.endpoint edge.succ = network.endpoint 0 ∨
      network.endpoint edge.succ = ((network.endpoint 0).2, (network.endpoint 0).1)) :
    network.deleteHead.VertexConnectedOn vertices := by
  intro removed hremoved
  rw [network.augmentedGraph_deleteHead_eq_of_parallel hparallel]
  exact hconnected removed hremoved

theorem VertexConnectedOn.deleteHead_of_direct
    {network : IndexedNetwork Vertex (edges + 1)} {vertices : Finset Vertex}
    (hconnected : network.VertexConnectedOn vertices)
    (hdirect : network.endpoint 0 = (network.source, network.target) ∨
      network.endpoint 0 = (network.target, network.source)) :
    network.deleteHead.VertexConnectedOn vertices := by
  intro removed hremoved
  rw [network.augmentedGraph_deleteHead_eq_of_direct hdirect]
  exact hconnected removed hremoved

end IndexedNetwork
end
end Universality.Section4

#print axioms Universality.Section4.preconnected_of_surjective_weak_map
#print axioms Universality.Section4.IndexedNetwork.vertexConnectedOn_iff_active
#print axioms Universality.Section4.IndexedNetwork.VertexConnectedOn.delete_or_contract
