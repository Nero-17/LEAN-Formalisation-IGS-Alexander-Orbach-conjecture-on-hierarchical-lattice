import Universality.Percolation.HistoryTransition
import Universality.Percolation.LocalLabelLaw
import Universality.Percolation.SubstitutionMass

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Conditional expected population after one actual graph refinement. -/
theorem refinement_liveCount (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (coarse : Configuration outerEdges) (σ τ : LiveState) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        ((R.substitute S).liveCount σ τ (substitutionConfigurationEquiv cells) : ℝ)) =
      R.liveResponse σ coarse (fun state => S.massMatrix p state τ) := by
  classical
  have hlocal (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        ((R.substitute S).liveCount σ τ (substitutionConfigurationEquiv cells) : ℝ) =
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        ∑ e, (R.localLiveCount S coarse (cells e) σ τ e : ℝ) := by
    rw [← S.coarse_fiber_conditional_joint_weight]
    by_cases hcoarse : S.coarseConfiguration cells = coarse
    · rw [R.substitute_liveCount, R.substitutedLiveCount_eq_local, hcoarse, Nat.cast_sum]
    · simp [hcoarse]
  simp_rw [hlocal, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold liveResponse
  apply Finset.sum_congr rfl
  intro edge _
  rw [finite_product_local_moment (fun e cell => S.conditionalCellWeight p (coarse e) cell)
    (fun cell => (R.localLiveCount S coarse cell σ τ edge : ℝ)) edge]
  have hnorm (e : Fin outerEdges) : ∑ cell, S.conditionalCellWeight p (coarse e) cell = 1 :=
    S.sum_conditionalCellWeight p hpositive hless _
  simp_rw [hnorm]
  simp only [Finset.prod_const_one, one_mul]
  rw [← S.conditionalCellResponse_eq_weighted_sum]
  have h := R.localLiveCount_conditional_response S p symmetry hs ht coarse σ τ edge
  cases hchild : R.childState σ coarse edge <;> simpa only [hchild] using h

theorem refinement_liveResponse (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (coarse : Configuration outerEdges) (σ : LiveState) (values : LiveState → ℝ) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        (R.substitute S).liveResponse σ (substitutionConfigurationEquiv cells) values) =
      R.liveResponse σ coarse (S.massMatrix p *ᵥ values) := by
  simp_rw [(R.substitute S).liveResponse_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul,
    R.refinement_liveCount S p hpositive hless symmetry hs ht]
  simp_rw [R.liveResponse_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state _
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem liveResponse_smul (σ : LiveState) (coarse : Configuration outerEdges)
    (values : LiveState → ℝ) (scale : ℝ) :
    R.liveResponse σ coarse (scale • values) = scale * R.liveResponse σ coarse values := by
  simp only [liveResponse_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro state _
  ring

end
end Universality.FiniteNetwork

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork Matrix
open scoped BigOperators

theorem refinementWeight_liveResponse (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (n : ℕ) (coarse : Configuration (rule.generation n).edges)
    (state : LiveState) (values : LiveState → ℝ) :
    (∑ fine, refinementWeight rule p n coarse fine *
      (rule.generation (n + 1)).network.liveResponse state fine values) =
    (rule.generation n).network.liveResponse state coarse (rule.network.massMatrix p *ᵥ values) := by
  classical
  change (∑ fine : Configuration ((rule.generation n).edges * rule.edges),
    (∏ e, rule.network.conditionalCellWeight p (coarse e)
      (substitutionConfigurationEquiv.symm fine e)) *
    ((rule.generation n).network.substitute rule.network).liveResponse state fine values) = _
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  exact (rule.generation n).network.refinement_liveResponse rule.network p
    (by rwa [hfixed]) (by rwa [hfixed]) symmetry hs ht coarse state values

end
end Universality.Rule.ConfigurationHistory
