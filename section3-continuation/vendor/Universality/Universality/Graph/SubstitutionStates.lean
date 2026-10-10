import Universality.Graph.Substitution
import Universality.Percolation.TerminalSymmetry
import Mathlib.Tactic.Tauto

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

def substitutedActive (σ : LiveState) (ω : Fin outerEdges → Configuration innerEdges)
    (v : R.SubstitutionVertex S) : Bool := by
  classical
  exact decide ((R.substitutedGraph S ω).Reachable (Sum.inl R.source) v ∨
    (σ = .both ∧ (R.substitutedGraph S ω).Reachable (Sum.inl R.target) v))

theorem substitutedActive_cell (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) (e : Fin outerEdges) (x : Fin innerVertices) :
    R.substitutedActive S σ ω (R.cellVertex S e x) =
      ((R.active σ (S.coarseConfiguration ω) (R.endpoint e).1 &&
        (S.openGraph (ω e)).reachableDecide S.source x) ||
       (R.active σ (S.coarseConfiguration ω) (R.endpoint e).2 &&
        (S.openGraph (ω e)).reachableDecide S.target x)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [substitutedActive, decide_eq_true_eq, substitutedReachable_iff_active,
    substitutionActive_cell, Bool.or_eq_true, Bool.and_eq_true, active,
    SimpleGraph.reachableDecide_eq_true, beq_iff_eq]
  tauto

theorem reachableDecide_source_eq_target_of_crosses
    (ω : Configuration innerEdges) (hcross : S.crosses ω = true) (v : Fin innerVertices) :
    (S.openGraph ω).reachableDecide S.source v =
      (S.openGraph ω).reachableDecide S.target v := by
  apply Bool.eq_iff_iff.mpr
  rw [SimpleGraph.reachableDecide_eq_true, SimpleGraph.reachableDecide_eq_true]
  have h := (S.crosses_eq_true ω).mp hcross
  exact ⟨fun hs => h.symm.trans hs, fun ht => h.trans ht⟩

def substitutedChildState (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) (e : Fin outerEdges) (f : Fin innerEdges) :
    Option LiveState :=
  let first := R.substitutedActive S σ ω (R.cellVertex S e (S.endpoint f).1)
  let second := R.substitutedActive S σ ω (R.cellVertex S e (S.endpoint f).2)
  if first && second then
    if ω e f then some .connected else some .both
  else if first || second then some .single else none

/-- The orientation-sensitive local state.  Terminal symmetry is used later
to identify the two single-terminal expectations, not assumed here. -/
def localChildState (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) (e : Fin outerEdges) (f : Fin innerEdges) :
    Option LiveState :=
  if R.active σ (S.coarseConfiguration ω) (R.endpoint e).1 then
    if R.active σ (S.coarseConfiguration ω) (R.endpoint e).2 then
      if S.crosses (ω e) then S.childState .connected (ω e) f
      else S.childState .both (ω e) f
    else S.childState .single (ω e) f
  else
    if R.active σ (S.coarseConfiguration ω) (R.endpoint e).2 then
      S.reverse.childState .single (ω e) f
    else none

theorem substitutedChildState_eq_local (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) (e : Fin outerEdges) (f : Fin innerEdges) :
    R.substitutedChildState S σ ω e f = R.localChildState S σ ω e f := by
  unfold substitutedChildState localChildState
  rw [substitutedActive_cell, substitutedActive_cell]
  cases ha : R.active σ (S.coarseConfiguration ω) (R.endpoint e).1 <;>
    cases hb : R.active σ (S.coarseConfiguration ω) (R.endpoint e).2
  · simp
  · simp only [Bool.false_and, Bool.true_and, Bool.false_or, Bool.false_eq_true,
      Bool.true_eq, ↓reduceIte]
    simp [childState, active, reverse, show (LiveState.single == LiveState.both) = false from by decide]
    rfl
  · simp only [Bool.false_and, Bool.true_and, Bool.or_false, Bool.false_eq_true,
      Bool.true_eq, ↓reduceIte]
    simp [childState, active, show (LiveState.single == LiveState.both) = false from by decide]
  · cases hc : S.crosses (ω e)
    · simp only [Bool.true_and, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [Bool.true_and, Bool.true_eq, ↓reduceIte]
      rw [S.reachableDecide_source_eq_target_of_crosses (ω e) hc,
        S.reachableDecide_source_eq_target_of_crosses (ω e) hc]
      simp only [Bool.or_self]
      simp only [childState, active, show (LiveState.connected == LiveState.both) = false from by decide, Bool.false_and, Bool.or_false,
        S.reachableDecide_source_eq_target_of_crosses (ω e) hc]

end
end Universality.FiniteNetwork
