import Universality.Arithmetic.FixedPointCoefficientSign

/-! The nondegenerate single-edge base for strict coefficient positivity. -/

namespace Universality.Section4.IndexedNetwork

noncomputable section
variable {V : Type*} [DecidableEq V]

theorem normalizedCoefficient_single_edge (network : IndexedNetwork V 1)
    (vertices : Finset V) (hsupport : network.SupportedOn vertices)
    (hconnected : network.ConnectedOn vertices)
    (hloopless : (network.endpoint 0).1 ≠ (network.endpoint 0).2)
    (hterminals : network.source ≠ network.target) :
    network.normalizedCoefficient vertices = 1 := by
  have hcontractSupport := hsupport.contractHead hloopless
  have hcontractConnected := hconnected.contractHead
  have hsingleton : vertices.erase (network.endpoint 0).1 = {network.contractHead.source} := by
    ext vertex
    simp only [Finset.mem_singleton]
    constructor
    · intro hvertex
      exact ((network.contractHead.linked_empty_iff_eq _ _ _).mp
        (hcontractConnected vertex hvertex)).symm
    · intro hequal
      exact hequal ▸ hcontractSupport.1
  have hcard : vertices.card = 2 := by
    have h := hsupport.contractHead_card
    rw [hsingleton, Finset.card_singleton] at h
    exact h.symm
  have hcontractTerminals : network.contractHead.source = network.contractHead.target :=
    (network.contractHead.linked_empty_iff_eq _ _ _).mp
      (hcontractConnected _ hcontractSupport.2.1)
  have hcontract : network.contractHead.signedCoefficient = 1 := by
    rw [signedCoefficient_empty, if_pos hcontractTerminals]
  have hdelete : network.deleteHead.signedCoefficient = 0 := by
    rw [signedCoefficient_empty]
    exact if_neg hterminals
  rw [normalizedCoefficient, network.signedCoefficient_delete_contract, hcontract, hdelete, hcard]
  norm_num

end
end Universality.Section4.IndexedNetwork

#print axioms Universality.Section4.IndexedNetwork.normalizedCoefficient_single_edge
