import Universality.Percolation.CoarseRootLaw
import Universality.Graph.InternalIncidentEdges
import Universality.Probability.FiniteProductMomentPointBound

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem rootChildState_ne_inactive_of_incident (R : FiniteNetwork vertices edges)
    (root : Fin vertices) (coarse : Configuration edges) (edge : Fin edges)
    (hincident : edge ∈ R.incidentEdges root) : R.rootChildState root coarse edge ≠ .inactive := by
  have hroot : (R.openGraph coarse).reachableDecide root root = true := by
    rw [SimpleGraph.reachableDecide_eq_true]
  obtain hfirst | hsecond := (Finset.mem_filter.mp hincident).2
  · simp only [rootChildState, hfirst, hroot, orientedStateOf, ↓reduceIte]
    cases (R.openGraph coarse).reachableDecide root (R.endpoint edge).2 <;> cases coarse edge <;> decide
  · simp only [rootChildState, hsecond, hroot, orientedStateOf, ↓reduceIte]
    cases (R.openGraph coarse).reachableDecide root (R.endpoint edge).1 <;> cases coarse edge <;> decide

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem root_child_atom_bound
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (bound : ℝ)
    (hpoint : ∀ (child : LiveState) (size : ℕ), S.conditionalInternalMassProbability p
      (child == .connected) true (child == .both) size ≤ bound)
    (root : Fin outerVertices) (coarse : Configuration outerEdges) (edge : Fin outerEdges)
    (hincident : edge ∈ R.incidentEdges root) (size : ℕ) :
    (∑ cell : Configuration innerEdges,
      if S.internalStateMass (R.rootChildState root coarse edge) cell = size
      then S.conditionalCellWeight p (coarse edge) cell else 0) ≤ bound := by
  have hne := R.rootChildState_ne_inactive_of_incident root coarse edge hincident
  obtain ⟨child, hchild⟩ : ∃ child, (R.rootChildState root coarse edge).eraseOrientation = some child := by
    cases hstate : R.rootChildState root coarse edge <;> simp_all [OrientedState.eraseOrientation]
  change S.conditionalInternalMassProbability p (coarse edge)
    (R.rootChildState root coarse edge).sourceSelected
    (R.rootChildState root coarse edge).targetSelected size ≤ bound
  rw [R.root_child_conditional_mass_probability S symmetry hs ht p hpositive hless root coarse edge child hchild]
  exact hpoint child size

theorem coarseRootMassObservable_atom_bound
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (bound : ℝ)
    (hpoint : ∀ (child : LiveState) (size : ℕ), S.conditionalInternalMassProbability p
      (child == .connected) true (child == .both) size ≤ bound)
    (root : Fin outerVertices) (edge : Fin outerEdges)
    (hincident : edge ∈ R.incidentEdges root) (size : ℕ) :
    R.coarseRootMassObservable S p root (fun mass => if mass = size then 1 else 0) ≤ bound := by
  rw [R.coarseRootMassObservable_disintegration S p hpositive hless]
  calc
    _ ≤ ∑ coarse : Configuration outerEdges, bernoulliWeight (S.reliability p) coarse * bound := by
      apply Finset.sum_le_sum
      intro coarse _
      apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hpositive.le hless.le _)
      simp only [mul_ite, mul_one, mul_zero]
      exact finite_product_atom_bound
        (fun e cell => S.conditionalCellWeight p (coarse e) cell)
        (fun e cell => S.internalStateMass (R.rootChildState root coarse e) cell)
        (fun e cell => S.conditionalCellWeight_nonneg hp hp' _ _)
        (fun e => S.sum_conditionalCellWeight p hpositive hless (coarse e))
        edge bound (R.root_child_atom_bound S symmetry hs ht p hpositive hless bound hpoint root coarse edge hincident)
        (R.clusterVertices coarse root).card size
    _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

theorem coarseRootMassObservable_point_power_bound
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hpoint : ∀ (child : LiveState) (size : ℕ), S.conditionalInternalMassProbability p
      (child == .connected) true (child == .both) size ≤ bound)
    (root : Fin outerVertices) (first second : Fin outerEdges) (hdistinct : second ≠ first)
    (hfirst : first ∈ R.incidentEdges root) (hsecond : second ∈ R.incidentEdges root) (order size : ℕ) :
    (size : ℝ) ^ order * R.coarseRootMassObservable S p root (fun mass => if mass = size then 1 else 0) ≤
      2 ^ (order + 1) * bound * R.coarseRootMassObservable S p root (fun mass => (mass : ℝ) ^ order) := by
  rw [R.coarseRootMassObservable_disintegration S p hpositive hless,
    R.coarseRootMassObservable_disintegration S p hpositive hless]
  simp only [mul_ite, mul_one, mul_zero]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro coarse _
  have hbranch := finite_product_two_live_point_bound
    (fun e cell => S.conditionalCellWeight p (coarse e) cell)
    (fun e cell => S.internalStateMass (R.rootChildState root coarse e) cell)
    (fun e cell => S.conditionalCellWeight_nonneg hp hp' _ _)
    (fun e => S.sum_conditionalCellWeight p hpositive hless (coarse e))
    first second hdistinct bound hbound
    (R.root_child_atom_bound S symmetry hs ht p hpositive hless bound hpoint root coarse first hfirst)
    (R.root_child_atom_bound S symmetry hs ht p hpositive hless bound hpoint root coarse second hsecond)
    (R.clusterVertices coarse root).card order size
  have hscaled := mul_le_mul_of_nonneg_left hbranch (bernoulliWeight_nonneg hpositive.le hless.le coarse)
  nlinarith

end
end Universality.FiniteNetwork


