import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

namespace IGSIII.Geometry

 theorem sigmaCongr_subtype_point {Index Other Point : Type*}
    {firstPredicate : Index → Point → Prop} {lastPredicate : Other → Point → Prop}
    (base : Index ≃ Other)
    (equivalent : ∀ index point, firstPredicate index point ↔ lastPredicate (base index) point)
    (pair : Σ index, {point // firstPredicate index point}) :
    ((Equiv.sigmaCongr (β₁ := fun index => {point // firstPredicate index point})
      (β₂ := fun index => {point // lastPredicate index point}) base (fun index => Equiv.subtypeEquivRight (equivalent index))) pair).2.val = pair.2.val := rfl

 theorem sigmaCongr_subtype_index {Index Other Point : Type*}
    {firstPredicate : Index → Point → Prop} {lastPredicate : Other → Point → Prop}
    (base : Index ≃ Other)
    (equivalent : ∀ index point, firstPredicate index point ↔ lastPredicate (base index) point)
    (pair : Σ index, {point // firstPredicate index point}) :
    ((Equiv.sigmaCongr (β₁ := fun index => {point // firstPredicate index point})
      (β₂ := fun index => {point // lastPredicate index point}) base (fun index => Equiv.subtypeEquivRight (equivalent index))) pair).1 = base pair.1 := rfl

 theorem sigmaAssocProd_subtype_point {First Last Point : Type*} {predicate : First → Last → Point → Prop}
    (pair : Σ index : First × Last, {point // predicate index.1 index.2 point}) :
    (Equiv.sigmaAssocProd (γ := fun first last => {point // predicate first last point}) pair).2.2.val = pair.2.val := rfl

 theorem sigmaAssocProd_subtype_first {First Last Point : Type*} {predicate : First → Last → Point → Prop}
    (pair : Σ index : First × Last, {point // predicate index.1 index.2 point}) :
    (Equiv.sigmaAssocProd (γ := fun first last => {point // predicate first last point}) pair).1 = pair.1.1 := rfl

 theorem sigmaAssocProd_subtype_last {First Last Point : Type*} {predicate : First → Last → Point → Prop}
    (pair : Σ index : First × Last, {point // predicate index.1 index.2 point}) :
    (Equiv.sigmaAssocProd (γ := fun first last => {point // predicate first last point}) pair).2.1 = pair.1.2 := rfl


theorem sigmaCongr_index {Index Other : Type*} {firstFiber : Index → Type*}
    {lastFiber : Other → Type*} (base : Index ≃ Other)
    (fiber : ∀ index, firstFiber index ≃ lastFiber (base index)) (pair : Σ index, firstFiber index) :
    (Equiv.sigmaCongr base fiber pair).1 = base pair.1 := rfl

theorem dependentMap_heq {Index : Type*} {firstFiber lastFiber : Index → Type*}
    (map : ∀ index, firstFiber index → lastFiber index) {first last : Index}
    (indexEquality : first = last) {point : firstFiber first} {other : firstFiber last}
    (pointEquality : HEq point other) : HEq (map first point) (map last other) := by
  cases indexEquality
  cases pointEquality
  rfl

def consSubtypeEquiv {Choice Point : Type*} (age : ℕ)
    (predicate : (Fin (age + 1) → Choice) → Point → Prop)
    (tailPredicate : Choice → (Fin age → Choice) → Point → Prop)
    (equivalent : ∀ word point, predicate word point ↔
      tailPredicate (word 0) (fun index => word index.succ) point) :
    (Σ word, {point // predicate word point}) ≃
      Σ head, Σ tail, {point // tailPredicate head tail point} :=
  (Equiv.sigmaCongr (Fin.consEquiv (fun _ : Fin (age + 1) => Choice)).symm
    (fun word => Equiv.subtypeEquivRight (equivalent word))).trans
      (Equiv.sigmaAssocProd (γ := fun head tail => {point // tailPredicate head tail point}))

theorem consSubtypeEquiv_head {Choice Point : Type*} (age : ℕ)
    (predicate : (Fin (age + 1) → Choice) → Point → Prop)
    (tailPredicate : Choice → (Fin age → Choice) → Point → Prop)
    (equivalent : ∀ word point, predicate word point ↔
      tailPredicate (word 0) (fun index => word index.succ) point)
    (pair : Σ word, {point // predicate word point}) :
    (consSubtypeEquiv age predicate tailPredicate equivalent pair).1 = pair.1 0 := rfl

theorem consSubtypeEquiv_word {Choice Point : Type*} (age : ℕ)
    (predicate : (Fin (age + 1) → Choice) → Point → Prop)
    (tailPredicate : Choice → (Fin age → Choice) → Point → Prop)
    (equivalent : ∀ word point, predicate word point ↔
      tailPredicate (word 0) (fun index => word index.succ) point)
    (pair : Σ word, {point // predicate word point}) :
    (consSubtypeEquiv age predicate tailPredicate equivalent pair).2.1 =
      (fun index => pair.1 index.succ) := rfl

theorem consSubtypeEquiv_point {Choice Point : Type*} (age : ℕ)
    (predicate : (Fin (age + 1) → Choice) → Point → Prop)
    (tailPredicate : Choice → (Fin age → Choice) → Point → Prop)
    (equivalent : ∀ word point, predicate word point ↔
      tailPredicate (word 0) (fun index => word index.succ) point)
    (pair : Σ word, {point // predicate word point}) :
    (consSubtypeEquiv age predicate tailPredicate equivalent pair).2.2.val = pair.2.val := rfl
end IGSIII.Geometry