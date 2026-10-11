import Universality.Arithmetic.FixedPointDeletionContraction

/-! Active-vertex bookkeeping for the deletion–contraction induction. -/

namespace Universality.Section4.IndexedNetwork

noncomputable section
variable {V : Type*} [DecidableEq V] {edges : ℕ}

def SupportedOn (network : IndexedNetwork V edges) (vertices : Finset V) : Prop :=
  network.source ∈ vertices ∧ network.target ∈ vertices ∧
    ∀ edge, (network.endpoint edge).1 ∈ vertices ∧ (network.endpoint edge).2 ∈ vertices

def ConnectedOn (network : IndexedNetwork V edges) (vertices : Finset V) : Prop :=
  ∀ vertex ∈ vertices, network.Linked (fun _ => true) network.source vertex

omit [DecidableEq V] in
theorem SupportedOn.deleteHead {network : IndexedNetwork V (edges + 1)} {vertices : Finset V}
    (hsupport : network.SupportedOn vertices) : network.deleteHead.SupportedOn vertices :=
  ⟨hsupport.1, hsupport.2.1, fun edge => hsupport.2.2 edge.succ⟩

theorem merge_mem_erase {vertices : Finset V} {first second vertex : V}
    (hsecond : second ∈ vertices)
    (hdistinct : first ≠ second) (hvertex : vertex ∈ vertices) :
    merge first second vertex ∈ vertices.erase first := by
  by_cases hequal : vertex = first
  · simp only [hequal, merge_first]
    exact Finset.mem_erase.mpr ⟨hdistinct.symm, hsecond⟩
  · simp only [merge, if_neg hequal]
    exact Finset.mem_erase.mpr ⟨hequal, hvertex⟩

theorem SupportedOn.contractHead {network : IndexedNetwork V (edges + 1)} {vertices : Finset V}
    (hsupport : network.SupportedOn vertices)
    (hdistinct : (network.endpoint 0).1 ≠ (network.endpoint 0).2) :
    network.contractHead.SupportedOn (vertices.erase (network.endpoint 0).1) := by
  have hmerge {vertex : V} (hvertex : vertex ∈ vertices) :
      merge (network.endpoint 0).1 (network.endpoint 0).2 vertex ∈ vertices.erase (network.endpoint 0).1 :=
    merge_mem_erase (hsupport.2.2 0).2 hdistinct hvertex
  exact ⟨hmerge hsupport.1, hmerge hsupport.2.1, fun edge =>
    ⟨hmerge (hsupport.2.2 edge.succ).1, hmerge (hsupport.2.2 edge.succ).2⟩⟩

theorem ConnectedOn.contractHead {network : IndexedNetwork V (edges + 1)} {vertices : Finset V}
    (hconnected : network.ConnectedOn vertices) :
    network.contractHead.ConnectedOn (vertices.erase (network.endpoint 0).1) := by
  intro vertex hvertex
  have hmember := Finset.mem_erase.mp hvertex
  have hfull : (Fin.cons true (fun _ : Fin edges => true) : Fin (edges + 1) → Bool) =
      fun _ => true := by
    ext edge
    exact Fin.cases rfl (fun _ => rfl) edge
  have hlinked := (network.linked_contractHead (fun _ => true) network.source vertex).mp
    (by simpa only [hfull] using hconnected vertex hmember.2)
  change network.contractHead.Linked (fun _ => true)
    (merge (network.endpoint 0).1 (network.endpoint 0).2 network.source) vertex
  simpa only [merge, if_neg hmember.1] using hlinked

theorem SupportedOn.contractHead_card {network : IndexedNetwork V (edges + 1)}
    {vertices : Finset V} (hsupport : network.SupportedOn vertices) :
    (vertices.erase (network.endpoint 0).1).card + 1 = vertices.card :=
  Finset.card_erase_add_one (hsupport.2.2 0).1

@[simp] theorem merge_same (first vertex : V) : merge first first vertex = vertex := by
  by_cases hequal : vertex = first <;> simp [merge, hequal]

theorem contractHead_eq_deleteHead_of_loop (network : IndexedNetwork V (edges + 1))
    (hloop : (network.endpoint 0).1 = (network.endpoint 0).2) :
    network.contractHead = network.deleteHead := by
  cases network
  simp_all only [contractHead, deleteHead, merge_same]

theorem signedCoefficient_eq_zero_of_head_loop (network : IndexedNetwork V (edges + 1))
    (hloop : (network.endpoint 0).1 = (network.endpoint 0).2) :
    network.signedCoefficient = 0 := by
  rw [network.signedCoefficient_delete_contract, network.contractHead_eq_deleteHead_of_loop hloop,
    sub_self]

theorem signedCoefficient_eq_zero_of_loop (network : IndexedNetwork V edges)
    (hloop : ∃ edge, (network.endpoint edge).1 = (network.endpoint edge).2) :
    network.signedCoefficient = 0 := by
  induction edges with
  | zero => obtain ⟨edge, _⟩ := hloop; exact Fin.elim0 edge
  | succ edges ih =>
      obtain ⟨edge, hloop⟩ := hloop
      refine Fin.cases (fun hloop => ?_) (fun edge hloop => ?_) edge hloop
      · exact network.signedCoefficient_eq_zero_of_head_loop hloop
      · rw [network.signedCoefficient_delete_contract,
          ih network.deleteHead ⟨edge, hloop⟩,
          ih network.contractHead ⟨edge, congrArg (merge (network.endpoint 0).1 (network.endpoint 0).2) hloop⟩,
          sub_self]

omit [DecidableEq V] in
theorem signedCoefficient_coincident_terminals (network : IndexedNetwork V (edges + 1))
    (hequal : network.source = network.target) : network.signedCoefficient = 0 := by
  classical
  unfold signedCoefficient
  simp only [← hequal, Linked, Relation.EqvGen.refl, ↓reduceIte]
  rw [← Fintype.prod_sum (fun (_ : Fin (edges + 1)) (state : Bool) =>
    if state = true then (1 : ℤ) else -1)]
  simp

omit [DecidableEq V] in
theorem linked_empty_iff_eq (network : IndexedNetwork V 0)
    (configuration : Fin 0 → Bool) (first second : V) :
    network.Linked configuration first second ↔ first = second := by
  constructor
  · intro h
    induction h with
    | rel first second h => obtain ⟨edge, _⟩ := h; exact Fin.elim0 edge
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihfirst ihsecond => exact ihfirst.trans ihsecond
  · intro hequal
    subst second
    exact Relation.EqvGen.refl _

theorem signedCoefficient_empty (network : IndexedNetwork V 0) :
    network.signedCoefficient = if network.source = network.target then 1 else 0 := by
  classical
  simp [signedCoefficient, linked_empty_iff_eq]
end
end Universality.Section4.IndexedNetwork



