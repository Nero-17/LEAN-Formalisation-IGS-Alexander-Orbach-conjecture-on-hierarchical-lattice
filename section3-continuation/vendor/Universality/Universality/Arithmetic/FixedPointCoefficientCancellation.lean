import Universality.Arithmetic.FixedPointDeletionContraction

/-!
Cancellation of the signed top coefficient when a Bernoulli coordinate is
irrelevant, and vanishing when even the fully open graph does not connect the
terminals. These statements allow loops, repeated edges, and coincident
terminals; they impose no connectedness convention on the vertex type.
-/

namespace Universality.Section4.IndexedNetwork

noncomputable section
open scoped BigOperators

variable {V : Type*} {edges : ℕ}

theorem signedCoefficient_eq_zero_of_head_invariant
    (network : IndexedNetwork V (edges + 1))
    (hinvariant : ∀ configuration : Fin edges → Bool,
      network.Linked (Fin.cons true configuration) network.source network.target ↔
        network.Linked (Fin.cons false configuration) network.source network.target) :
    network.signedCoefficient = 0 := by
  classical
  unfold signedCoefficient
  rw [← (Fin.consEquiv (fun _ : Fin (edges + 1) => Bool)).sum_comp]
  change (∑ pair : Bool × (Fin edges → Bool),
    if network.Linked (Fin.cons pair.1 pair.2) network.source network.target then
      ∏ edge : Fin (edges + 1),
        if (Fin.cons pair.1 pair.2 : Fin (edges + 1) → Bool) edge = true then (1 : ℤ) else -1
    else 0) = 0
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro configuration _
  rw [hinvariant configuration]
  split_ifs <;> simp

theorem signedCoefficient_eq_zero_of_not_linked_full
    (network : IndexedNetwork V edges)
    (hdisconnected : ¬ network.Linked (fun _ => true) network.source network.target) :
    network.signedCoefficient = 0 := by
  classical
  unfold signedCoefficient
  apply Finset.sum_eq_zero
  intro configuration _
  have hnotlinked : ¬ network.Linked configuration network.source network.target := by
    intro hlinked
    apply hdisconnected
    exact Relation.EqvGen.mono (fun first second h => by
      obtain ⟨edge, _, hendpoint⟩ := h
      exact ⟨edge, rfl, hendpoint⟩) _ _ hlinked
  exact if_neg hnotlinked

end
end Universality.Section4.IndexedNetwork

#print axioms Universality.Section4.IndexedNetwork.signedCoefficient_eq_zero_of_head_invariant
#print axioms Universality.Section4.IndexedNetwork.signedCoefficient_eq_zero_of_not_linked_full
