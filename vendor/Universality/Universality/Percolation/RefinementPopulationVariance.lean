import Universality.Percolation.LocalPopulationBounds

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem localLiveResponse_second_moment_le (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (coarse : Configuration outerEdges) (state : LiveState) (edge : Fin outerEdges)
    (values : LiveState → ℝ) :
    (∑ cell, S.conditionalCellWeight p (coarse edge) cell *
      R.localLiveResponse S coarse cell state edge values ^ 2) ≤
      match R.childState state coarse edge with
      | none => 0
      | some _ => (innerEdges * ∑ child, |values child|) ^ 2 := by
  cases hchild : R.childState state coarse edge with
  | none => simp only [R.localLiveResponse_inactive S coarse _ state edge values hchild,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero, le_refl]
  | some child =>
    calc
      _ ≤ ∑ cell, S.conditionalCellWeight p (coarse edge) cell *
          (innerEdges * ∑ child, |values child|) ^ 2 := by
        apply Finset.sum_le_sum
        intro cell _
        apply mul_le_mul_of_nonneg_left _ (S.conditionalCellWeight_nonneg hp hp' _ _)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (R.localLiveResponse_abs_le S coarse cell state edge values) 2
      _ = _ := by
        rw [← Finset.sum_mul, S.sum_conditionalCellWeight p hpositive hless, one_mul]

/-- The actual weighted population has conditional innovation variance at
most a fixed constant per live coarse cell, for arbitrary real weights. -/
theorem refinement_liveResponse_variance_le (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (coarse : Configuration outerEdges) (state : LiveState) (values : LiveState → ℝ) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) *
      ((R.substitute S).liveResponse state (substitutionConfigurationEquiv cells) values -
        R.liveResponse state coarse (S.massMatrix p *ᵥ values)) ^ 2) ≤
      R.liveResponse state coarse (fun _ => (innerEdges * ∑ child, |values child|) ^ 2) := by
  classical
  have hmean : R.liveResponse state coarse (S.massMatrix p *ᵥ values) =
      ∑ edge, ∑ cell, S.conditionalCellWeight p (coarse edge) cell *
        R.localLiveResponse S coarse cell state edge values := by
    unfold liveResponse
    apply Finset.sum_congr rfl
    intro edge _
    exact (R.localLiveResponse_conditional_mean S p symmetry hs ht coarse state edge values).symm
  have hlocal (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) *
      ((R.substitute S).liveResponse state (substitutionConfigurationEquiv cells) values -
        R.liveResponse state coarse (S.massMatrix p *ᵥ values)) ^ 2 =
      (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) *
      ((∑ edge, R.localLiveResponse S coarse (cells edge) state edge values) -
        R.liveResponse state coarse (S.massMatrix p *ᵥ values)) ^ 2 := by
    rw [← S.coarse_fiber_conditional_joint_weight]
    by_cases hcoarse : S.coarseConfiguration cells = coarse
    · rw [R.refinement_liveResponse_local S coarse cells state values hcoarse]
    · simp [hcoarse]
  simp_rw [hlocal]
  rw [hmean]
  apply (finite_product_variance_le_second_moments
    (fun edge cell => S.conditionalCellWeight p (coarse edge) cell)
    (fun edge cell => R.localLiveResponse S coarse cell state edge values)
    (fun edge => S.sum_conditionalCellWeight p hpositive hless (coarse edge))).trans
  unfold liveResponse
  exact Finset.sum_le_sum (fun edge _ =>
    R.localLiveResponse_second_moment_le S p hp hp' hpositive hless coarse state edge values)

end
end Universality.FiniteNetwork
