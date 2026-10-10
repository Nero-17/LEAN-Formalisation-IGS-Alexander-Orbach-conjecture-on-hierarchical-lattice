import Universality.Percolation.GenerationMomentRecursion
import Universality.Percolation.VertexMassResponse

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def conditionalVertexMoment (R : FiniteNetwork vertices edges) (p : ℝ) (state : LiveState) (r : ℕ) : ℝ :=
  R.conditionalInternalMoment p (state == .connected) true (state == .both) r

theorem conditionalVertexMoment_one (R : FiniteNetwork vertices edges) (p : ℝ) (state : LiveState) :
    R.conditionalVertexMoment p state 1 = R.conditionalVertexMass p state :=
  R.conditionalInternalMoment_one p _ _ _

theorem conditionalInternalMoment_inactive (R : FiniteNetwork vertices edges) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) (opened : Bool) (r : ℕ) :
    R.conditionalInternalMoment p opened false false r = if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst r
    exact R.conditionalInternalMoment_zero p hpositive hless opened false false
  · simp [conditionalInternalMoment, internalSelectedMass, selectedActive, hr, zero_pow hr]

theorem conditionalInternalMoment_connected (R : FiniteNetwork vertices edges) (p : ℝ) (r : ℕ) :
    R.conditionalInternalMoment p true true true r = R.conditionalInternalMoment p true true false r := by
  unfold conditionalInternalMoment
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases hcross : R.crosses configuration = true
  · rw [R.internalSelectedMass_connected configuration hcross]
  · simp [conditionalCellWeight, hcross]

theorem conditionalInternalMoment_oriented (R : FiniteNetwork vertices edges)
    (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (parent : OrientedState) (opened : Bool) (r : ℕ)
    (hstate : parent ≠ .inactive → (parent = .connected ↔ opened = true)) :
    R.conditionalInternalMoment p opened parent.sourceSelected parent.targetSelected r =
      match parent.eraseOrientation with
      | none => if r = 0 then 1 else 0
      | some state => R.conditionalVertexMoment p state r := by
  cases parent <;> cases opened <;>
    simp_all [OrientedState.sourceSelected, OrientedState.targetSelected,
      OrientedState.eraseOrientation, conditionalVertexMoment]
  all_goals first
    | exact R.conditionalInternalMoment_connected p r
    | exact R.conditionalInternalMoment_inactive p hpositive hless _ r
    | exact symmetry.conditionalInternalMoment_swap hs ht p false false true r
    | rfl

theorem child_conditionalVertexMoment
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (state : LiveState) (coarse : Configuration outerEdges) (edge : Fin outerEdges) (r : ℕ) :
    S.conditionalInternalMoment p (coarse edge)
      (R.orientedChildState true (state == .both) coarse edge).sourceSelected
      (R.orientedChildState true (state == .both) coarse edge).targetSelected r =
      match R.childState state coarse edge with
      | none => if r = 0 then 1 else 0
      | some child => S.conditionalVertexMoment p child r := by
  rw [S.conditionalInternalMoment_oriented symmetry hs ht p hpositive hless _ (coarse edge) r
    (fun hlive => R.live_oriented_state_determines_crossing true (state == .both) coarse edge hlive),
    R.eraseOrientation_orientedChildState]

end
end Universality.FiniteNetwork
