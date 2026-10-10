import Universality.Percolation.RefinementMean
import Universality.Percolation.VertexMassResponse

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem refinement_vertexMass (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (coarse : Configuration outerEdges) (state : LiveState) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        ((R.substitute S).internalSelectedMass true (state == .both)
          (substitutionConfigurationEquiv cells) : ℝ)) =
      (R.internalSelectedMass true (state == .both) coarse : ℝ) +
        R.liveResponse state coarse (S.conditionalVertexMass p) := by
  classical
  have hlocal (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        ((R.substitute S).internalSelectedMass true (state == .both)
          (substitutionConfigurationEquiv cells) : ℝ) =
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        ((R.internalSelectedMass true (state == .both) coarse : ℝ) +
          ∑ e, (S.internalStateMass (R.orientedChildState true (state == .both) coarse e)
            (cells e) : ℝ)) := by
    rw [← S.coarse_fiber_conditional_joint_weight]
    by_cases hcoarse : S.coarseConfiguration cells = coarse
    · rw [R.internalSelectedMass_substitute, hcoarse, Nat.cast_add, Nat.cast_sum]
    · simp [hcoarse]
  simp_rw [hlocal]
  rw [S.conditional_product_additive_response p hpositive hless coarse
    (R.internalSelectedMass true (state == .both) coarse : ℝ)
    (fun e cell => (S.internalStateMass (R.orientedChildState true (state == .both) coarse e) cell : ℝ))]
  congr 1
  unfold liveResponse
  apply Finset.sum_congr rfl
  intro edge _
  change S.conditionalInternalMean p (coarse edge)
    (R.orientedChildState true (state == .both) coarse edge).sourceSelected
    (R.orientedChildState true (state == .both) coarse edge).targetSelected = _
  have h := R.child_conditionalVertexMass S symmetry hs ht p state coarse edge
  cases hchild : R.childState state coarse edge <;> simpa only [hchild] using h

end
end Universality.FiniteNetwork

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork
open scoped BigOperators

theorem refinementWeight_vertexMass (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (n : ℕ) (coarse : Configuration (rule.generation n).edges) (state : LiveState) :
    (∑ fine, refinementWeight rule p n coarse fine *
      ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) fine : ℝ)) =
      ((rule.generation n).network.internalSelectedMass true (state == .both) coarse : ℝ) +
        (rule.generation n).network.liveResponse state coarse (rule.network.conditionalVertexMass p) := by
  classical
  change (∑ fine : Configuration ((rule.generation n).edges * rule.edges),
    (∏ e, rule.network.conditionalCellWeight p (coarse e)
      (substitutionConfigurationEquiv.symm fine e)) *
    (((rule.generation n).network.substitute rule.network).internalSelectedMass true
      (state == .both) fine : ℝ)) = _
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  exact (rule.generation n).network.refinement_vertexMass rule.network p
    (by rwa [hfixed]) (by rwa [hfixed]) symmetry hs ht coarse state

end
end Universality.Rule.ConfigurationHistory
