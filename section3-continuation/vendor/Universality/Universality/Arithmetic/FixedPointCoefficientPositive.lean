import Universality.Arithmetic.FixedPointSingleEdge
import Universality.Arithmetic.FixedPointConnectedFromVertex

/-!
Strict positivity of the normalized top coefficient. The induction uses
actual indexed minors, retains all parallel-edge variables, and handles the
single-edge case before choosing a positive minor. No beta-invariant theorem
or top-coefficient nonvanishing premise is assumed.
-/

namespace Universality.Section4.IndexedNetwork

noncomputable section
variable {V : Type*} [DecidableEq V] {edges : ℕ}

theorem normalizedCoefficient_pos (network : IndexedNetwork V edges)
    (vertices : Finset V) (hsupport : network.SupportedOn vertices)
    (hconnected : network.ConnectedOn vertices)
    (hloopless : ∀ edge, (network.endpoint edge).1 ≠ (network.endpoint edge).2)
    (hterminals : network.source ≠ network.target)
    (hvertexConnected : network.VertexConnectedOn vertices) :
    0 < network.normalizedCoefficient vertices := by
  induction edges generalizing vertices with
  | zero =>
      exact False.elim (hterminals ((network.linked_empty_iff_eq _ _ _).mp
        (hconnected network.target hsupport.2.1)))
  | succ edges ih =>
      by_cases hempty : edges = 0
      · subst edges
        rw [network.normalizedCoefficient_single_edge vertices hsupport hconnected
          (hloopless 0) hterminals]
        norm_num
      have hedges : 0 < edges := Nat.pos_of_ne_zero hempty
      have hcontractNonnegative := normalizedCoefficient_nonnegative network.contractHead
        (vertices.erase (network.endpoint 0).1) (hsupport.contractHead (hloopless 0))
        hconnected.contractHead
      have hdeletePositive (hdeleteVertex : network.deleteHead.VertexConnectedOn vertices) :
          0 < network.deleteHead.normalizedCoefficient vertices := by
        exact ih network.deleteHead vertices hsupport.deleteHead
          (hdeleteVertex.connectedOn hsupport.deleteHead (fun edge => hloopless edge.succ)
            hterminals hedges)
          (fun edge => hloopless edge.succ) hterminals hdeleteVertex
      by_cases hparallel : ∃ edge : Fin edges, network.endpoint edge.succ = network.endpoint 0 ∨
          network.endpoint edge.succ = ((network.endpoint 0).2, (network.endpoint 0).1)
      · rw [network.normalizedCoefficient_delete_contract vertices hsupport]
        exact add_pos_of_nonneg_of_pos hcontractNonnegative
          (hdeletePositive (hvertexConnected.deleteHead_of_parallel hparallel))
      by_cases hdirect : network.endpoint 0 = (network.source, network.target) ∨
          network.endpoint 0 = (network.target, network.source)
      · rw [network.normalizedCoefficient_delete_contract vertices hsupport]
        exact add_pos_of_nonneg_of_pos hcontractNonnegative
          (hdeletePositive (hvertexConnected.deleteHead_of_direct hdirect))
      rcases hvertexConnected.delete_or_contract hsupport (hloopless 0) with
        hdeleteVertex | hcontractVertex
      · rw [network.normalizedCoefficient_delete_contract vertices hsupport]
        exact add_pos_of_nonneg_of_pos hcontractNonnegative (hdeletePositive hdeleteVertex)
      · have hcontractLoopless := network.contractHead_loopless hloopless (by
          intro edge
          exact ⟨fun hequal => hparallel ⟨edge, Or.inl hequal⟩,
            fun hequal => hparallel ⟨edge, Or.inr hequal⟩⟩)
        have hcontractTerminals := network.contractHead_terminals_distinct hterminals
          ⟨fun hequal => hdirect (Or.inl hequal), fun hequal => hdirect (Or.inr hequal)⟩
        have hcontractPositive := ih network.contractHead
          (vertices.erase (network.endpoint 0).1) (hsupport.contractHead (hloopless 0))
          hconnected.contractHead hcontractLoopless hcontractTerminals hcontractVertex
        have hdeleteNonnegative := network.normalizedCoefficient_deleteHead_nonnegative
          vertices hsupport hconnected hloopless hterminals hvertexConnected
        rw [network.normalizedCoefficient_delete_contract vertices hsupport]
        exact add_pos_of_pos_of_nonneg hcontractPositive hdeleteNonnegative

end
end Universality.Section4.IndexedNetwork

#print axioms Universality.Section4.IndexedNetwork.normalizedCoefficient_pos
