import Universality.Arithmetic.FixedPointBridge
import Universality.Arithmetic.FixedPointActiveVertices
import Universality.Arithmetic.FixedPointCoefficientCancellation

/-! The sign of the top reliability coefficient for a connected indexed
network, including loops, parallel edges and coincident terminals. -/

namespace Universality.Section4.IndexedNetwork
noncomputable section
variable {V : Type*} [DecidableEq V] {edges : ℕ}

/-- The parity-equivalent exponent `edges + vertices.card + 1` avoids
truncated subtraction in the usual sign `edges + 1 - vertices.card`. -/
def normalizedCoefficient (network : IndexedNetwork V edges) (vertices : Finset V) : ℤ :=
  (-1 : ℤ) ^ (edges + vertices.card + 1) * network.signedCoefficient

omit [DecidableEq V] in
theorem ConnectedOn.deleteHead_of_linked
    {network : IndexedNetwork V (edges + 1)} {vertices : Finset V}
    (hconnected : network.ConnectedOn vertices)
    (hhead : network.deleteHead.Linked (fun _ => true)
      (network.endpoint 0).1 (network.endpoint 0).2) :
    network.deleteHead.ConnectedOn vertices := by
  intro vertex hvertex
  have hfull : (Fin.cons true (fun _ : Fin edges => true) : Fin (edges + 1) → Bool) =
      fun _ => true := by
    ext edge
    exact Fin.cases rfl (fun _ => rfl) edge
  have hlinked := (network.linked_head_iff (fun _ => true) network.source vertex).mp
    (by simpa only [hfull] using hconnected vertex hvertex)
  rcases hlinked with h | ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · exact h
  · exact Relation.EqvGen.trans _ _ _ hfirst (Relation.EqvGen.trans _ _ _ hhead hsecond)
  · exact Relation.EqvGen.trans _ _ _ hfirst
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hhead) hsecond)

theorem normalizedCoefficient_delete_contract
    (network : IndexedNetwork V (edges + 1)) (vertices : Finset V)
    (hsupport : network.SupportedOn vertices) :
    network.normalizedCoefficient vertices =
      network.contractHead.normalizedCoefficient (vertices.erase (network.endpoint 0).1) +
        network.deleteHead.normalizedCoefficient vertices := by
  simp only [normalizedCoefficient, network.signedCoefficient_delete_contract,
    ← hsupport.contractHead_card, pow_add, pow_one]
  ring

theorem normalizedCoefficient_nonnegative (network : IndexedNetwork V edges)
    (vertices : Finset V) (hsupport : network.SupportedOn vertices)
    (hconnected : network.ConnectedOn vertices) :
    0 ≤ network.normalizedCoefficient vertices := by
  induction edges generalizing vertices with
  | zero =>
      have hsingleton : vertices = {network.source} := by
        ext vertex
        simp only [Finset.mem_singleton]
        constructor
        · intro hvertex
          exact ((network.linked_empty_iff_eq _ _ _).mp
            (hconnected vertex hvertex)).symm
        · intro hequal
          exact hequal ▸ hsupport.1
      have hterminals : network.source = network.target :=
        (network.linked_empty_iff_eq _ _ _).mp (hconnected network.target hsupport.2.1)
      simp [normalizedCoefficient, signedCoefficient_empty, hterminals, hsingleton]
  | succ edges ih =>
      by_cases hloop : (network.endpoint 0).1 = (network.endpoint 0).2
      · simp [normalizedCoefficient, network.signedCoefficient_eq_zero_of_head_loop hloop]
      have hcontract := ih network.contractHead _ (hsupport.contractHead hloop)
        hconnected.contractHead
      by_cases hhead : network.deleteHead.Linked (fun _ => true)
          (network.endpoint 0).1 (network.endpoint 0).2
      · have hdelete := ih network.deleteHead vertices hsupport.deleteHead
          (hconnected.deleteHead_of_linked hhead)
        rw [network.normalizedCoefficient_delete_contract vertices hsupport]
        exact add_nonneg hcontract hdelete
      · by_cases hterminals : network.deleteHead.Linked (fun _ => true)
            network.source network.target
        · have hzero := network.signedCoefficient_eq_zero_of_head_invariant
            (network.linked_head_iff_of_bridge hhead hterminals)
          simp [normalizedCoefficient, hzero]
        · have hzero := network.deleteHead.signedCoefficient_eq_zero_of_not_linked_full hterminals
          rw [network.normalizedCoefficient_delete_contract vertices hsupport]
          simpa only [normalizedCoefficient, hzero, mul_zero, add_zero] using hcontract

end
end Universality.Section4.IndexedNetwork

#print axioms Universality.Section4.IndexedNetwork.normalizedCoefficient_nonnegative