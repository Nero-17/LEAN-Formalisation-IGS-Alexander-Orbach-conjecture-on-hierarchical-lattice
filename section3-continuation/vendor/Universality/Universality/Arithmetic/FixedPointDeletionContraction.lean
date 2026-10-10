import Universality.Arithmetic.FixedPointDegree
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
An endpoint-indexed deletion–contraction model. Loops and coincident terminals
are allowed, so minors retain every remaining Bernoulli variable.
-/

namespace Universality.Section4

noncomputable section
open scoped BigOperators

structure IndexedNetwork (V : Type*) (edges : ℕ) where
  endpoint : Fin edges → V × V
  source : V
  target : V

namespace IndexedNetwork

variable {V : Type*} {edges : ℕ}

def Linked (network : IndexedNetwork V edges) (configuration : Fin edges → Bool) : V → V → Prop :=
  Relation.EqvGen (fun first second => ∃ edge,
    configuration edge = true ∧ network.endpoint edge = (first, second))

def signedCoefficient (network : IndexedNetwork V edges) : ℤ := by
  classical
  exact
  ∑ configuration : Fin edges → Bool,
    if network.Linked configuration network.source network.target then
      ∏ edge : Fin edges, if configuration edge then (1 : ℤ) else -1
    else 0

def deleteHead (network : IndexedNetwork V (edges + 1)) : IndexedNetwork V edges where
  endpoint edge := network.endpoint edge.succ
  source := network.source
  target := network.target

def merge [DecidableEq V] (first second vertex : V) : V :=
  if vertex = first then second else vertex

@[simp] theorem merge_first [DecidableEq V] (first second : V) :
    merge first second first = second := by simp [merge]

@[simp] theorem merge_second [DecidableEq V] (first second : V) :
    merge first second second = second := by
  by_cases hequal : second = first <;> simp [merge, hequal]

def contractHead [DecidableEq V] (network : IndexedNetwork V (edges + 1)) : IndexedNetwork V edges where
  endpoint edge :=
    (merge (network.endpoint 0).1 (network.endpoint 0).2 (network.endpoint edge.succ).1,
      merge (network.endpoint 0).1 (network.endpoint 0).2 (network.endpoint edge.succ).2)
  source := merge (network.endpoint 0).1 (network.endpoint 0).2 network.source
  target := merge (network.endpoint 0).1 (network.endpoint 0).2 network.target

theorem linked_deleteHead (network : IndexedNetwork V (edges + 1))
    (configuration : Fin edges → Bool) (first second : V) :
    network.Linked (Fin.cons false configuration) first second ↔
      network.deleteHead.Linked configuration first second := by
  constructor
  · apply Relation.EqvGen.mono
    intro first second h
    obtain ⟨edge, hopen, hedge⟩ := h
    refine Fin.cases ?_ (fun edge hopen hedge => ?_) edge hopen hedge
    · simp
    · exact ⟨edge, hopen, hedge⟩
  · apply Relation.EqvGen.mono
    intro first second h
    obtain ⟨edge, hopen, hedge⟩ := h
    exact ⟨edge.succ, hopen, hedge⟩

theorem linked_merge [DecidableEq V] (network : IndexedNetwork V (edges + 1))
    (configuration : Fin edges → Bool) (vertex : V) :
    network.Linked (Fin.cons true configuration) vertex
      (merge (network.endpoint 0).1 (network.endpoint 0).2 vertex) := by
  by_cases hvertex : vertex = (network.endpoint 0).1
  · rw [hvertex, merge_first]
    exact Relation.EqvGen.rel _ _ ⟨0, rfl, Prod.eta _⟩
  · simp only [merge, if_neg hvertex]
    exact Relation.EqvGen.refl _

theorem linked_contractHead [DecidableEq V] (network : IndexedNetwork V (edges + 1))
    (configuration : Fin edges → Bool) (first second : V) :
    network.Linked (Fin.cons true configuration) first second ↔
      network.contractHead.Linked configuration
        (merge (network.endpoint 0).1 (network.endpoint 0).2 first)
        (merge (network.endpoint 0).1 (network.endpoint 0).2 second) := by
  constructor
  · intro h
    induction h with
    | rel first second h =>
        obtain ⟨edge, hopen, hedge⟩ := h
        revert hopen hedge
        refine Fin.cases ?_ (fun edge hopen hedge => ?_) edge
        · intro _ hedge
          have hfirst := congrArg Prod.fst hedge
          have hsecond := congrArg Prod.snd hedge
          simp only at hfirst hsecond
          rw [← hfirst, ← hsecond, merge_first, merge_second]
          exact Relation.EqvGen.refl _
        · exact Relation.EqvGen.rel _ _ ⟨edge, hopen, by
            change (_, _) = (_, _)
            rw [hedge]⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ihfirst ihsecond => exact Relation.EqvGen.trans _ _ _ ihfirst ihsecond
  · intro h
    have hlift : ∀ {left right}, network.contractHead.Linked configuration left right →
        network.Linked (Fin.cons true configuration) left right := by
      intro left right h
      induction h with
      | rel left right h =>
          obtain ⟨edge, hopen, hedge⟩ := h
          have horiginal : network.Linked (Fin.cons true configuration)
              (network.endpoint edge.succ).1 (network.endpoint edge.succ).2 :=
            Relation.EqvGen.rel _ _ ⟨edge.succ, hopen, Prod.eta _⟩
          have hmerged := Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (network.linked_merge configuration (network.endpoint edge.succ).1))
            (Relation.EqvGen.trans _ _ _ horiginal
              (network.linked_merge configuration (network.endpoint edge.succ).2))
          have hleft := congrArg Prod.fst hedge
          have hright := congrArg Prod.snd hedge
          change merge _ _ _ = left at hleft
          change merge _ _ _ = right at hright
          rw [← hleft, ← hright]
          exact hmerged
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ihfirst ihsecond => exact Relation.EqvGen.trans _ _ _ ihfirst ihsecond
    exact Relation.EqvGen.trans _ _ _ (network.linked_merge configuration first)
      (Relation.EqvGen.trans _ _ _ (hlift h)
        (Relation.EqvGen.symm _ _ (network.linked_merge configuration second)))

theorem signedCoefficient_delete_contract [DecidableEq V]
    (network : IndexedNetwork V (edges + 1)) :
    network.signedCoefficient = network.contractHead.signedCoefficient -
      network.deleteHead.signedCoefficient := by
  classical
  unfold signedCoefficient
  rw [← (Fin.consEquiv (fun _ : Fin (edges + 1) => Bool)).sum_comp]
  change (∑ pair : Bool × (Fin edges → Bool),
    if network.Linked (Fin.cons pair.1 pair.2) network.source network.target then
      ∏ edge : Fin (edges + 1), if (Fin.cons pair.1 pair.2 : Fin (edges + 1) → Bool) edge = true then (1 : ℤ) else -1
    else 0) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul,
    linked_deleteHead, linked_contractHead]
  change (∑ configuration : Fin edges → Bool,
    if network.contractHead.Linked configuration network.contractHead.source network.contractHead.target
    then _ else 0) + (∑ configuration : Fin edges → Bool,
    if network.deleteHead.Linked configuration network.deleteHead.source network.deleteHead.target
    then _ else 0) = _
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro configuration _
  split_ifs <;> simp
end IndexedNetwork
end
end Universality.Section4


