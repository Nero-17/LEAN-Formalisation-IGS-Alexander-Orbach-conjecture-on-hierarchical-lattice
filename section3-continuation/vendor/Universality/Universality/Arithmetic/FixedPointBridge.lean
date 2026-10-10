import Universality.Arithmetic.FixedPointDeletionContraction

namespace Universality.Section4.IndexedNetwork
noncomputable section

variable {V : Type*} {edges : ℕ}

theorem linked_mono (network : IndexedNetwork V edges)
    {firstConfiguration secondConfiguration : Fin edges → Bool}
    (hle : ∀ edge, firstConfiguration edge = true → secondConfiguration edge = true)
    {first second : V} (hlinked : network.Linked firstConfiguration first second) :
    network.Linked secondConfiguration first second := by
  apply Relation.EqvGen.mono _ _ _ hlinked
  intro left right h
  obtain ⟨edge, hopen, hendpoint⟩ := h
  exact ⟨edge, hle edge hopen, hendpoint⟩

theorem linked_full (network : IndexedNetwork V edges)
    {configuration : Fin edges → Bool} {first second : V}
    (hlinked : network.Linked configuration first second) :
    network.Linked (fun _ => true) first second :=
  network.linked_mono (fun _ _ => rfl) hlinked

/-- Opening one distinguished edge joins precisely its two preexisting
components. The formula remains valid for loops and coincident terminals. -/
theorem linked_head_iff (network : IndexedNetwork V (edges + 1))
    (configuration : Fin edges → Bool) (first second : V) :
    network.Linked (Fin.cons true configuration) first second ↔
      network.deleteHead.Linked configuration first second ∨
      (network.deleteHead.Linked configuration first (network.endpoint 0).1 ∧
        network.deleteHead.Linked configuration (network.endpoint 0).2 second) ∨
      (network.deleteHead.Linked configuration first (network.endpoint 0).2 ∧
        network.deleteHead.Linked configuration (network.endpoint 0).1 second) := by
  constructor
  · intro hlinked
    induction hlinked with
    | rel left right h =>
      obtain ⟨edge, hopen, hendpoint⟩ := h
      revert hopen hendpoint
      refine Fin.cases ?_ (fun edge hopen hendpoint => ?_) edge
      · intro _ hendpoint
        have hleft := congrArg Prod.fst hendpoint
        have hright := congrArg Prod.snd hendpoint
        simp only at hleft hright
        exact Or.inr (Or.inl ⟨hleft ▸ Relation.EqvGen.refl _, hright ▸ Relation.EqvGen.refl _⟩)
      · exact Or.inl (Relation.EqvGen.rel _ _ ⟨edge, hopen, hendpoint⟩)
    | refl vertex => exact Or.inl (Relation.EqvGen.refl vertex)
    | symm left right _ ih =>
      rcases ih with h | ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
      · exact Or.inl (Relation.EqvGen.symm _ _ h)
      · exact Or.inr (Or.inr ⟨Relation.EqvGen.symm _ _ hsecond, Relation.EqvGen.symm _ _ hfirst⟩)
      · exact Or.inr (Or.inl ⟨Relation.EqvGen.symm _ _ hsecond, Relation.EqvGen.symm _ _ hfirst⟩)
    | trans left middle right _ _ ihfirst ihsecond =>
      rcases ihfirst with h | ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
      · rcases ihsecond with h' | ⟨hfirst', hsecond'⟩ | ⟨hfirst', hsecond'⟩
        · exact Or.inl (Relation.EqvGen.trans _ _ _ h h')
        · exact Or.inr (Or.inl ⟨Relation.EqvGen.trans _ _ _ h hfirst', hsecond'⟩)
        · exact Or.inr (Or.inr ⟨Relation.EqvGen.trans _ _ _ h hfirst', hsecond'⟩)
      · rcases ihsecond with h' | ⟨hfirst', hsecond'⟩ | ⟨hfirst', hsecond'⟩
        · exact Or.inr (Or.inl ⟨hfirst, Relation.EqvGen.trans _ _ _ hsecond h'⟩)
        · exact Or.inr (Or.inl ⟨hfirst, hsecond'⟩)
        · exact Or.inl (Relation.EqvGen.trans _ _ _ hfirst hsecond')
      · rcases ihsecond with h' | ⟨hfirst', hsecond'⟩ | ⟨hfirst', hsecond'⟩
        · exact Or.inr (Or.inr ⟨hfirst, Relation.EqvGen.trans _ _ _ hsecond h'⟩)
        · exact Or.inl (Relation.EqvGen.trans _ _ _ hfirst hsecond')
        · exact Or.inr (Or.inr ⟨hfirst, hsecond'⟩)
  · intro hlinked
    have hlift {left right : V} (h : network.deleteHead.Linked configuration left right) :
        network.Linked (Fin.cons true configuration) left right := by
      apply Relation.EqvGen.mono _ _ _ h
      intro first second h
      obtain ⟨edge, hopen, hendpoint⟩ := h
      exact ⟨edge.succ, hopen, hendpoint⟩
    have hhead : network.Linked (Fin.cons true configuration)
        (network.endpoint 0).1 (network.endpoint 0).2 :=
      Relation.EqvGen.rel _ _ ⟨0, rfl, Prod.eta _⟩
    rcases hlinked with h | ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact hlift h
    · exact Relation.EqvGen.trans _ _ _ (hlift hfirst)
        (Relation.EqvGen.trans _ _ _ hhead (hlift hsecond))
    · exact Relation.EqvGen.trans _ _ _ (hlift hfirst)
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hhead) (hlift hsecond))

/-- A full-graph bridge cannot change terminal connectivity when the two
terminals already lie on the same side of that bridge. -/
theorem linked_head_iff_of_bridge (network : IndexedNetwork V (edges + 1))
    (hbridge : ¬ network.deleteHead.Linked (fun _ => true)
      (network.endpoint 0).1 (network.endpoint 0).2)
    (hterminals : network.deleteHead.Linked (fun _ => true) network.source network.target)
    (configuration : Fin edges → Bool) :
    network.Linked (Fin.cons true configuration) network.source network.target ↔
      network.Linked (Fin.cons false configuration) network.source network.target := by
  rw [linked_head_iff, linked_deleteHead]
  constructor
  · intro h
    rcases h with h | ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact h
    · exact False.elim (hbridge (Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (network.deleteHead.linked_full hfirst))
        (Relation.EqvGen.trans _ _ _ hterminals
          (Relation.EqvGen.symm _ _ (network.deleteHead.linked_full hsecond)))))
    · exact False.elim (hbridge (Relation.EqvGen.trans _ _ _
        (network.deleteHead.linked_full hsecond)
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hterminals)
          (network.deleteHead.linked_full hfirst))))
  · exact Or.inl

end
end Universality.Section4.IndexedNetwork

#print axioms Universality.Section4.IndexedNetwork.linked_head_iff
#print axioms Universality.Section4.IndexedNetwork.linked_head_iff_of_bridge
