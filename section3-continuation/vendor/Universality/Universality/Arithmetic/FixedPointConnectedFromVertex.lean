import Universality.Arithmetic.GraphIndexedVertexConnectivity
import Universality.Arithmetic.GraphEdgeNonbridge
import Universality.Arithmetic.FixedPointCoefficientSign

namespace Universality.Section4.IndexedNetwork
noncomputable section
variable {V : Type*} [DecidableEq V] {edges : ℕ}

omit [DecidableEq V] in
theorem linked_of_augmented_reachable (network : IndexedNetwork V edges)
    (hterminals : network.Linked (fun _ => true) network.source network.target)
    {first second : V} (hreachable : network.augmentedGraph.Reachable first second) :
    network.Linked (fun _ => true) first second := by
  obtain ⟨walk⟩ := hreachable
  induction walk with
  | nil => exact Relation.EqvGen.refl _
  | @cons first middle last hadj walk ih =>
      have hstep : network.Linked (fun _ => true) first middle := by
        rcases hadj with hadj | hadj
        · exact (network.linked_iff_reachable _ _ _).mpr hadj.reachable
        · rcases (SimpleGraph.edge_adj _ _ _ _).mp hadj with ⟨hequal, _⟩
          rcases hequal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hterminals
          · exact Relation.EqvGen.symm _ _ hterminals
      exact Relation.EqvGen.trans _ _ _ hstep ih

 theorem finset_eq_pair_of_card_le_two {vertices : Finset V} {first second : V}
    (hfirst : first ∈ vertices) (hsecond : second ∈ vertices)
    (hdistinct : first ≠ second) (hcard : vertices.card ≤ 2) :
    vertices = {first, second} := by
  have hsubset : ({first, second} : Finset V) ⊆ vertices := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hfirst, hsecond⟩
  apply (Finset.eq_of_subset_of_card_le hsubset ?_).symm
  simpa only [Finset.card_pair hdistinct] using hcard

 theorem VertexConnectedOn.linked_terminals
    {network : IndexedNetwork V edges} {vertices : Finset V}
    (hvertex : network.VertexConnectedOn vertices) (hsupport : network.SupportedOn vertices)
    (hloopless : ∀ edge, (network.endpoint edge).1 ≠ (network.endpoint edge).2)
    (hterminals : network.source ≠ network.target) (hedges : 0 < edges) :
    network.Linked (fun _ => true) network.source network.target := by
  by_cases hcard : vertices.card ≤ 2
  · have hvertices := finset_eq_pair_of_card_le_two hsupport.1 hsupport.2.1 hterminals hcard
    let edge : Fin edges := ⟨0, hedges⟩
    have hfirst := (hsupport.2.2 edge).1
    have hsecond := (hsupport.2.2 edge).2
    rw [hvertices] at hfirst hsecond
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
    have hlinked : network.Linked (fun _ => true) (network.endpoint edge).1 (network.endpoint edge).2 :=
      Relation.EqvGen.rel _ _ ⟨edge, rfl, Prod.eta _⟩
    rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
    · exact False.elim (hloopless edge (hfirst.trans hsecond.symm))
    · simpa only [hfirst, hsecond] using hlinked
    · have hreverse : network.Linked (fun _ => true) network.target network.source := by
        simpa only [hfirst, hsecond] using hlinked
      exact Relation.EqvGen.symm _ _ hreverse
    · exact False.elim (hloopless edge (hfirst.trans hsecond.symm))
  · obtain ⟨third, hthird, hthirdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({network.source, network.target} : Finset V)) (t := vertices)
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hthirdnot
    let first : {vertex // vertex ∈ vertices} := ⟨network.source, hsupport.1⟩
    let second : {vertex // vertex ∈ vertices} := ⟨network.target, hsupport.2.1⟩
    have halternate := Universality.Section4.reachable_after_edge_deletion_of_vertex_preconnected
      ((network.vertexConnectedOn_iff_active vertices).mp hvertex) first second
      ⟨third, hthird⟩
      (fun hequal => hthirdnot.1 (congrArg Subtype.val hequal))
      (fun hequal => hthirdnot.2 (congrArg Subtype.val hequal))
    let homomorphism : (network.activeAugmentedGraph vertices).deleteEdges {s(first, second)} →g
        network.fullGraph :=
      { toFun := Subtype.val
        map_rel' := by
          intro left right hadj
          obtain ⟨hadj, hnotedge⟩ := SimpleGraph.deleteEdges_adj.mp hadj
          change network.augmentedGraph.Adj left.val right.val at hadj
          rcases hadj with hadj | hadj
          · exact hadj
          · exfalso
            simp only [Set.mem_singleton_iff] at hnotedge
            apply hnotedge
            rcases (SimpleGraph.edge_adj _ _ _ _).mp hadj with ⟨hequal, _⟩
            rcases hequal with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
            · have hleft' : left = first := Subtype.ext hleft
              have hright' : right = second := Subtype.ext hright
              rw [hleft', hright']
            · have hleft' : left = second := Subtype.ext hleft
              have hright' : right = first := Subtype.ext hright
              rw [hleft', hright']
              exact Sym2.eq_swap }
    exact (network.linked_iff_reachable _ _ _).mpr (halternate.map homomorphism)

 theorem VertexConnectedOn.connectedOn
    {network : IndexedNetwork V edges} {vertices : Finset V}
    (hvertex : network.VertexConnectedOn vertices) (hsupport : network.SupportedOn vertices)
    (hloopless : ∀ edge, (network.endpoint edge).1 ≠ (network.endpoint edge).2)
    (hterminals : network.source ≠ network.target) (hedges : 0 < edges) :
    network.ConnectedOn vertices := by
  have hlinked := hvertex.linked_terminals hsupport hloopless hterminals hedges
  intro vertex hmember
  by_cases hequal : vertex = network.target
  · simpa only [hequal] using hlinked
  have hsource : network.source ∈ vertices.erase network.target :=
    Finset.mem_erase.mpr ⟨hterminals, hsupport.1⟩
  have hvertexmem : vertex ∈ vertices.erase network.target :=
    Finset.mem_erase.mpr ⟨hequal, hmember⟩
  have hreachable := hvertex network.target hsupport.2.1 ⟨network.source, hsource⟩ ⟨vertex, hvertexmem⟩
  let homomorphism : network.augmentedGraph.induce (↑(vertices.erase network.target) : Set V) →g
      network.augmentedGraph :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  exact network.linked_of_augmented_reachable hlinked (hreachable.map homomorphism)

 theorem VertexConnectedOn.not_linked_terminals_of_bridge
    {network : IndexedNetwork V (edges + 1)} {vertices : Finset V}
    (hvertex : network.VertexConnectedOn vertices) (hsupport : network.SupportedOn vertices)
    (hhead : (network.endpoint 0).1 ≠ (network.endpoint 0).2)
    (hterminals : network.source ≠ network.target)
    (hbridge : ¬ network.deleteHead.Linked (fun _ => true)
      (network.endpoint 0).1 (network.endpoint 0).2) :
    ¬ network.deleteHead.Linked (fun _ => true) network.source network.target := by
  intro hlinked
  apply hbridge
  by_cases hcard : vertices.card ≤ 2
  · have hvertices := finset_eq_pair_of_card_le_two (hsupport.2.2 0).1 (hsupport.2.2 0).2 hhead hcard
    have hsource := hsupport.1
    have htarget := hsupport.2.1
    rw [hvertices] at hsource htarget
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsource htarget
    rcases hsource with hsource | hsource <;> rcases htarget with htarget | htarget
    · exact False.elim (hterminals (hsource.trans htarget.symm))
    · simpa only [hsource, htarget] using hlinked
    · have hreverse : network.deleteHead.Linked (fun _ => true)
          (network.endpoint 0).2 (network.endpoint 0).1 := by
        simpa only [hsource, htarget] using hlinked
      exact Relation.EqvGen.symm _ _ hreverse
    · exact False.elim (hterminals (hsource.trans htarget.symm))
  · obtain ⟨third, hthird, hthirdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({(network.endpoint 0).1, (network.endpoint 0).2} : Finset V)) (t := vertices)
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hthirdnot
    let first : {vertex // vertex ∈ vertices} := ⟨(network.endpoint 0).1, (hsupport.2.2 0).1⟩
    let second : {vertex // vertex ∈ vertices} := ⟨(network.endpoint 0).2, (hsupport.2.2 0).2⟩
    have halternate := Universality.Section4.reachable_after_edge_deletion_of_vertex_preconnected
      ((network.vertexConnectedOn_iff_active vertices).mp hvertex) first second
      ⟨third, hthird⟩
      (fun hequal => hthirdnot.1 (congrArg Subtype.val hequal))
      (fun hequal => hthirdnot.2 (congrArg Subtype.val hequal))
    let homomorphism : (network.activeAugmentedGraph vertices).deleteEdges {s(first, second)} →g
        network.deleteHead.augmentedGraph :=
      { toFun := Subtype.val
        map_rel' := by
          intro left right hadj
          apply network.augmentedGraph_deleteEdges_head_le
          obtain ⟨hadj, hnotedge⟩ := SimpleGraph.deleteEdges_adj.mp hadj
          refine SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩
          simp only [Set.mem_singleton_iff] at hnotedge ⊢
          intro hequal
          apply hnotedge
          rcases Sym2.eq_iff.mp hequal with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
          · have hleft' : left = first := Subtype.ext hleft
            have hright' : right = second := Subtype.ext hright
            rw [hleft', hright']
          · have hleft' : left = second := Subtype.ext hleft
            have hright' : right = first := Subtype.ext hright
            rw [hleft', hright']
            exact Sym2.eq_swap }
    exact network.deleteHead.linked_of_augmented_reachable hlinked (halternate.map homomorphism)

theorem normalizedCoefficient_deleteHead_nonnegative
    (network : IndexedNetwork V (edges + 1)) (vertices : Finset V)
    (hsupport : network.SupportedOn vertices) (hconnected : network.ConnectedOn vertices)
    (hloopless : ∀ edge, (network.endpoint edge).1 ≠ (network.endpoint edge).2)
    (hterminals : network.source ≠ network.target)
    (hvertex : network.VertexConnectedOn vertices) :
    0 ≤ network.deleteHead.normalizedCoefficient vertices := by
  by_cases hhead : network.deleteHead.Linked (fun _ => true)
      (network.endpoint 0).1 (network.endpoint 0).2
  · exact network.deleteHead.normalizedCoefficient_nonnegative vertices hsupport.deleteHead
      (hconnected.deleteHead_of_linked hhead)
  · have hzero := network.deleteHead.signedCoefficient_eq_zero_of_not_linked_full
      (hvertex.not_linked_terminals_of_bridge hsupport (hloopless 0) hterminals hhead)
    simp only [normalizedCoefficient, hzero, mul_zero, le_refl]
end
end Universality.Section4.IndexedNetwork

#print axioms Universality.Section4.IndexedNetwork.VertexConnectedOn.connectedOn
#print axioms Universality.Section4.IndexedNetwork.VertexConnectedOn.not_linked_terminals_of_bridge