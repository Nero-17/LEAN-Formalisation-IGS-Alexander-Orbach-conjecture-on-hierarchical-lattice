import Universality.Percolation.RefinementMean
import Universality.Probability.FiniteProductVariance

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def localLiveResponse (coarse : Configuration outerEdges) (cell : Configuration innerEdges)
    (state : LiveState) (edge : Fin outerEdges) (values : LiveState → ℝ) : ℝ :=
  ∑ child, (R.localLiveCount S coarse cell state child edge : ℝ) * values child

theorem localLiveCount_le (coarse : Configuration outerEdges) (cell : Configuration innerEdges)
    (state child : LiveState) (edge : Fin outerEdges) :
    R.localLiveCount S coarse cell state child edge ≤ innerEdges := by
  have hcount (T : FiniteNetwork innerVertices innerEdges) (parent : LiveState) :
      T.liveCount parent child cell ≤ innerEdges := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin innerEdges)
  unfold localLiveCount
  split_ifs <;> first | exact hcount _ _ | exact Nat.zero_le _

theorem localLiveResponse_abs_le (coarse : Configuration outerEdges) (cell : Configuration innerEdges)
    (state : LiveState) (edge : Fin outerEdges) (values : LiveState → ℝ) :
    |R.localLiveResponse S coarse cell state edge values| ≤ innerEdges * ∑ child, |values child| := by
  unfold localLiveResponse
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro child _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast R.localLiveCount_le S coarse cell state child edge)
    (abs_nonneg _)

theorem localLiveResponse_inactive (coarse : Configuration outerEdges) (cell : Configuration innerEdges)
    (state : LiveState) (edge : Fin outerEdges) (values : LiveState → ℝ)
    (hinactive : R.childState state coarse edge = none) :
    R.localLiveResponse S coarse cell state edge values = 0 := by
  unfold childState at hinactive
  unfold localLiveResponse localLiveCount
  cases hfirst : R.active state coarse (R.endpoint edge).1 <;>
    cases hsecond : R.active state coarse (R.endpoint edge).2 <;>
    cases hopen : coarse edge <;> simp_all

theorem refinement_liveResponse_local (coarse : Configuration outerEdges)
    (cells : Fin outerEdges → Configuration innerEdges) (state : LiveState) (values : LiveState → ℝ)
    (hcoarse : S.coarseConfiguration cells = coarse) :
    (R.substitute S).liveResponse state (substitutionConfigurationEquiv cells) values =
      ∑ edge, R.localLiveResponse S coarse (cells edge) state edge values := by
  rw [liveResponse_eq]
  simp_rw [R.substitute_liveCount S, R.substitutedLiveCount_eq_local S, hcoarse, Nat.cast_sum,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem localLiveResponse_conditional_mean (p : ℝ) (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (coarse : Configuration outerEdges) (state : LiveState) (edge : Fin outerEdges)
    (values : LiveState → ℝ) :
    (∑ cell, S.conditionalCellWeight p (coarse edge) cell *
      R.localLiveResponse S coarse cell state edge values) =
      match R.childState state coarse edge with
      | none => 0
      | some child => (S.massMatrix p *ᵥ values) child := by
  simp only [localLiveResponse, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← S.conditionalCellResponse_eq_weighted_sum,
    R.localLiveCount_conditional_response S p symmetry hs ht]
  cases hchild : R.childState state coarse edge <;>
    simp only [hchild, zero_mul, Finset.sum_const_zero, Matrix.mulVec, dotProduct]

end
end Universality.FiniteNetwork
