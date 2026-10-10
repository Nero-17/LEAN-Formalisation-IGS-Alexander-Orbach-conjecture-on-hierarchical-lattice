import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.DeriveFintype
import Universality.Graph.Reachability

/-!
# Finite two-terminal networks and conditional live-edge counts

Edges are individually indexed.  This permits independent Bernoulli edge states
and intermediate substitution networks, including the single edge.  Admissibility
of a classical rule is an additional property, not built into these expectations.
Connectivity here is mathlib's graph reachability, not an unexplained numerical
oracle.  At parameter 1/2 every edge configuration has the same weight.
-/

namespace Universality

structure FiniteNetwork (vertices edges : ℕ) where
  endpoint : Fin edges → Fin vertices × Fin vertices
  source : Fin vertices
  target : Fin vertices
  terminals_distinct : source ≠ target
  loopless : ∀ e, (endpoint e).1 ≠ (endpoint e).2

namespace FiniteNetwork

variable {vertices edges : ℕ}

abbrev Configuration (edges : ℕ) := Fin edges → Bool

def openGraph (R : FiniteNetwork vertices edges) (ω : Configuration edges) :
    SimpleGraph (Fin vertices) where
  Adj u v := u ≠ v ∧ ∃ e, ω e = true ∧
    ((R.endpoint e = (u, v)) ∨ (R.endpoint e = (v, u)))
  symm := ⟨by
    intro u v h
    rcases h with ⟨huv, e, he, huv' | hvu'⟩
    · exact ⟨Ne.symm huv, e, he, Or.inr huv'⟩
    · exact ⟨Ne.symm huv, e, he, Or.inl hvu'⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (R : FiniteNetwork vertices edges) (ω : Configuration edges) :
    DecidableRel (R.openGraph ω).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ ∃ _, _))

def crosses (R : FiniteNetwork vertices edges) (ω : Configuration edges) : Bool :=
  (R.openGraph ω).reachableDecide R.source R.target

theorem crosses_eq_true (R : FiniteNetwork vertices edges) (ω : Configuration edges) :
    R.crosses ω = true ↔ (R.openGraph ω).Reachable R.source R.target :=
  (R.openGraph ω).reachableDecide_eq_true _ _

inductive LiveState where
  | connected
  | both
  | single
  deriving DecidableEq, Fintype, Inhabited

def conditioning (R : FiniteNetwork vertices edges) (σ : LiveState)
    (ω : Configuration edges) : Bool :=
  match σ with
  | .connected => R.crosses ω
  | .both | .single => !(R.crosses ω)

def active (R : FiniteNetwork vertices edges) (σ : LiveState)
    (ω : Configuration edges) (v : Fin vertices) : Bool :=
  (R.openGraph ω).reachableDecide R.source v ||
    (σ == .both && (R.openGraph ω).reachableDecide R.target v)

def childState (R : FiniteNetwork vertices edges) (σ : LiveState)
    (ω : Configuration edges) (e : Fin edges) : Option LiveState :=
  let first := R.active σ ω (R.endpoint e).1
  let second := R.active σ ω (R.endpoint e).2
  if first && second then
    if ω e then some .connected else some .both
  else if first || second then some .single else none

def conditioningCount (R : FiniteNetwork vertices edges) (σ : LiveState) : ℕ :=
  (Finset.univ.filter fun ω : Configuration edges => R.conditioning σ ω = true).card

def liveCount (R : FiniteNetwork vertices edges) (σ τ : LiveState)
    (ω : Configuration edges) : ℕ :=
  (Finset.univ.filter fun e : Fin edges => R.childState σ ω e = some τ).card

def conditionalCount (R : FiniteNetwork vertices edges) (σ τ : LiveState) : ℕ :=
  ∑ ω : Configuration edges,
    if R.conditioning σ ω then R.liveCount σ τ ω else 0

/-- The conditional expectation at the fair parameter.  Its denominator is an
actual count of configurations.  Applications prove this denominator is positive. -/
def fairMassMatrix (R : FiniteNetwork vertices edges) : Matrix LiveState LiveState ℚ :=
  fun σ τ => (R.conditionalCount σ τ : ℚ) / R.conditioningCount σ

end FiniteNetwork
end Universality
