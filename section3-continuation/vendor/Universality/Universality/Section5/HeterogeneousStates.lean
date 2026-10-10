import Universality.Section5.HeterogeneousConnectivity
import Universality.Graph.SubstitutionStates
import Universality.Percolation.TerminalSymmetry
import Mathlib.Tactic.Tauto

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

def heterogeneousSubstitutedActive (σ : LiveState) (ω : (edge : Fin outerEdges) → Configuration (innerEdges edge))
    (v : R.HeterogeneousVertex S) : Bool := by
  classical
  exact decide ((R.heterogeneousSubstitutedGraph S ω).Reachable (Sum.inl R.source) v ∨
    (σ = .both ∧ (R.heterogeneousSubstitutedGraph S ω).Reachable (Sum.inl R.target) v))

theorem heterogeneousSubstitutedActive_cell (σ : LiveState)
    (ω : (edge : Fin outerEdges) → Configuration (innerEdges edge)) (e : Fin outerEdges) (x : Fin (innerVertices e)) :
    R.heterogeneousSubstitutedActive S σ ω (R.heterogeneousCellVertex S e x) =
      ((R.active σ (heterogeneousCoarseConfiguration S ω) (R.endpoint e).1 &&
        ((S e).openGraph (ω e)).reachableDecide (S e).source x) ||
       (R.active σ (heterogeneousCoarseConfiguration S ω) (R.endpoint e).2 &&
        ((S e).openGraph (ω e)).reachableDecide (S e).target x)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [heterogeneousSubstitutedActive, decide_eq_true_eq, heterogeneousSubstitutedReachable_iff_active,
    heterogeneousSubstitutionActive_cell, Bool.or_eq_true, Bool.and_eq_true, active,
    SimpleGraph.reachableDecide_eq_true, beq_iff_eq]
  tauto

def heterogeneousSubstitutedChildState (σ : LiveState)
    (ω : (edge : Fin outerEdges) → Configuration (innerEdges edge)) (e : Fin outerEdges) (f : Fin (innerEdges e)) :
    Option LiveState :=
  let first := R.heterogeneousSubstitutedActive S σ ω (R.heterogeneousCellVertex S e ((S e).endpoint f).1)
  let second := R.heterogeneousSubstitutedActive S σ ω (R.heterogeneousCellVertex S e ((S e).endpoint f).2)
  if first && second then
    if ω e f then some .connected else some .both
  else if first || second then some .single else none

/-- The orientation-sensitive local state.  Terminal symmetry is used later
to identify the two single-terminal expectations, not assumed here. -/
def heterogeneousLocalChildState (σ : LiveState)
    (ω : (edge : Fin outerEdges) → Configuration (innerEdges edge)) (e : Fin outerEdges) (f : Fin (innerEdges e)) :
    Option LiveState :=
  if R.active σ (heterogeneousCoarseConfiguration S ω) (R.endpoint e).1 then
    if R.active σ (heterogeneousCoarseConfiguration S ω) (R.endpoint e).2 then
      if (S e).crosses (ω e) then (S e).childState .connected (ω e) f
      else (S e).childState .both (ω e) f
    else (S e).childState .single (ω e) f
  else
    if R.active σ (heterogeneousCoarseConfiguration S ω) (R.endpoint e).2 then
      (S e).reverse.childState .single (ω e) f
    else none

theorem heterogeneousSubstitutedChildState_eq_local (σ : LiveState)
    (ω : (edge : Fin outerEdges) → Configuration (innerEdges edge)) (e : Fin outerEdges) (f : Fin (innerEdges e)) :
    R.heterogeneousSubstitutedChildState S σ ω e f = R.heterogeneousLocalChildState S σ ω e f := by
  unfold heterogeneousSubstitutedChildState heterogeneousLocalChildState
  rw [heterogeneousSubstitutedActive_cell, heterogeneousSubstitutedActive_cell]
  cases ha : R.active σ (heterogeneousCoarseConfiguration S ω) (R.endpoint e).1 <;>
    cases hb : R.active σ (heterogeneousCoarseConfiguration S ω) (R.endpoint e).2
  · simp
  · simp only [Bool.false_and, Bool.true_and, Bool.false_or, Bool.false_eq_true,
      Bool.true_eq, ↓reduceIte]
    simp [childState, active, reverse, show (LiveState.single == LiveState.both) = false from by decide]
    rfl
  · simp only [Bool.false_and, Bool.true_and, Bool.or_false, Bool.false_eq_true,
      Bool.true_eq, ↓reduceIte]
    simp [childState, active, show (LiveState.single == LiveState.both) = false from by decide]
  · cases hc : (S e).crosses (ω e)
    · simp only [Bool.true_and, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [Bool.true_and, Bool.true_eq, ↓reduceIte]
      rw [(S e).reachableDecide_source_eq_target_of_crosses (ω e) hc,
        (S e).reachableDecide_source_eq_target_of_crosses (ω e) hc]
      simp only [Bool.or_self]
      simp only [childState, active, show (LiveState.connected == LiveState.both) = false from by decide, Bool.false_and, Bool.or_false,
        (S e).reachableDecide_source_eq_target_of_crosses (ω e) hc]

end
end Universality.FiniteNetwork
