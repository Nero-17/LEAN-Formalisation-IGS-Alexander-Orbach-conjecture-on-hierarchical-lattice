import Universality.Percolation.InternalMassSymmetry

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
open Matrix

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Expected internal vertex mass in the manuscript's three reference states. -/
def conditionalVertexMass (R : FiniteNetwork vertices edges) (p : ℝ) (σ : LiveState) : ℝ :=
  R.conditionalInternalMean p (σ == .connected) true (σ == .both)

theorem conditionalInternalMean_inactive (R : FiniteNetwork vertices edges)
    (p : ℝ) (opened : Bool) : R.conditionalInternalMean p opened false false = 0 := by
  simp [conditionalInternalMean, internalSelectedMass, selectedActive]

theorem conditionalInternalMean_oriented (R : FiniteNetwork vertices edges)
    (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (parent : OrientedState) (opened : Bool)
    (hstate : parent ≠ .inactive → (parent = .connected ↔ opened = true)) :
    R.conditionalInternalMean p opened parent.sourceSelected parent.targetSelected =
      match parent.eraseOrientation with
      | none => 0
      | some σ => R.conditionalVertexMass p σ := by
  cases parent <;> cases opened <;>
    simp_all [OrientedState.sourceSelected, OrientedState.targetSelected,
      OrientedState.eraseOrientation, conditionalVertexMass]
  all_goals first
    | exact R.conditionalInternalMean_connected p
    | exact R.conditionalInternalMean_inactive p _
    | exact symmetry.conditionalInternalMean_swap hs ht p false false true
    | rfl

theorem conditionalCellWeight_reference (R : FiniteNetwork vertices edges)
    (p : ℝ) (σ : LiveState) (ω : Configuration edges) :
    R.conditionalCellWeight p (σ == .connected) ω =
      (if R.conditioning σ ω then bernoulliWeight p ω else 0) / R.conditioningProbability p σ := by
  cases σ <;>
    simp only [conditioningProbability_connected, conditioningProbability_both,
      conditioningProbability_single, conditionalCellWeight, conditioning]
  all_goals simp <;> rfl

theorem conditionalResponse_eq_weighted (R : FiniteNetwork vertices edges)
    (p : ℝ) (σ : LiveState) (values : LiveState → ℝ) :
    R.conditionalResponse p σ values =
      ∑ ω, R.conditionalCellWeight p (σ == .connected) ω * R.liveResponse σ ω values := by
  simp only [R.conditionalCellWeight_reference, conditionalResponse, div_mul_eq_mul_div,
    ← Finset.sum_div, ite_mul, zero_mul]

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem child_conditionalVertexMass (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (σ : LiveState) (coarse : Configuration outerEdges) (e : Fin outerEdges) :
    S.conditionalInternalMean p (coarse e)
      (R.orientedChildState true (σ == .both) coarse e).sourceSelected
      (R.orientedChildState true (σ == .both) coarse e).targetSelected =
      match R.childState σ coarse e with
      | none => 0
      | some τ => S.conditionalVertexMass p τ := by
  rw [S.conditionalInternalMean_oriented symmetry hs ht p _ (coarse e)
    (fun hlive => R.live_oriented_state_determines_crossing true (σ == .both) coarse e hlive)]
  rw [R.eraseOrientation_orientedChildState]

/-- Affine matrix recursion for actual vertex masses, valid off criticality.
The inhomogeneous term is the actual mean top-level internal reward. -/
theorem conditionalVertexMass_substitute (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (σ : LiveState) :
    (R.substitute S).conditionalVertexMass p σ =
      R.conditionalVertexMass (S.reliability p) σ +
        (R.massMatrix (S.reliability p) *ᵥ S.conditionalVertexMass p) σ := by
  change (R.substitute S).conditionalInternalMean p (σ == .connected) true (σ == .both) = _
  rw [R.conditionalInternalMean_substitute S p hpositive hless]
  simp_rw [R.child_conditionalVertexMass S symmetry hs ht]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  symm
  rw [R.massMatrix_mulVec_response, R.conditionalResponse_eq_weighted]
  rfl

end
end Universality.FiniteNetwork
