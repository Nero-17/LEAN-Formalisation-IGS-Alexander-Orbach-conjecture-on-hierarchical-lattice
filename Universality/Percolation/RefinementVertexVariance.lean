import Universality.Percolation.RefinementVertexMean
import Universality.Percolation.VertexMassMoments
import Universality.Probability.FiniteProductVariance

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Conditional independence eliminates cross terms in the actual refinement
reward. The variance is bounded by a live-cell response of second moments. -/
theorem refinement_vertexMass_variance_le (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (coarse : Configuration outerEdges) (state : LiveState) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        (((R.substitute S).internalSelectedMass true (state == .both)
          (substitutionConfigurationEquiv cells) : ℝ) -
          R.internalSelectedMass true (state == .both) coarse -
          R.liveResponse state coarse (S.conditionalVertexMass p)) ^ 2) ≤
      R.liveResponse state coarse (fun child => S.conditionalVertexMoment p child 2) := by
  classical
  have hmean : R.liveResponse state coarse (S.conditionalVertexMass p) =
      ∑ e, ∑ cell, S.conditionalCellWeight p (coarse e) cell *
        (S.internalStateMass (R.orientedChildState true (state == .both) coarse e) cell : ℝ) := by
    unfold liveResponse
    apply Finset.sum_congr rfl
    intro edge _
    exact (R.child_conditionalVertexMass S symmetry hs ht p state coarse edge).symm
  have hlocal (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        (((R.substitute S).internalSelectedMass true (state == .both)
          (substitutionConfigurationEquiv cells) : ℝ) -
          R.internalSelectedMass true (state == .both) coarse -
          R.liveResponse state coarse (S.conditionalVertexMass p)) ^ 2 =
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        ((∑ e, (S.internalStateMass (R.orientedChildState true (state == .both) coarse e)
          (cells e) : ℝ)) - R.liveResponse state coarse (S.conditionalVertexMass p)) ^ 2 := by
    rw [← S.coarse_fiber_conditional_joint_weight]
    by_cases hcoarse : S.coarseConfiguration cells = coarse
    · rw [R.internalSelectedMass_substitute, hcoarse, Nat.cast_add, Nat.cast_sum]
      ring
    · simp [hcoarse]
  simp_rw [hlocal]
  rw [hmean]
  apply (finite_product_variance_le_second_moments
    (fun e cell => S.conditionalCellWeight p (coarse e) cell)
    (fun e cell => (S.internalStateMass (R.orientedChildState true (state == .both) coarse e) cell : ℝ))
    (fun e => S.sum_conditionalCellWeight p hpositive hless (coarse e))).trans_eq
  unfold liveResponse
  apply Finset.sum_congr rfl
  intro edge _
  have h := R.child_conditionalVertexMoment S symmetry hs ht p hpositive hless state coarse edge 2
  change S.conditionalInternalMoment p (coarse edge)
    (R.orientedChildState true (state == .both) coarse edge).sourceSelected
    (R.orientedChildState true (state == .both) coarse edge).targetSelected 2 = _
  cases hchild : R.childState state coarse edge <;> simpa only [hchild, show (2 : ℕ) ≠ 0 by decide, if_false] using h

end
end Universality.FiniteNetwork
