import IGSIII34.Diffusion.BoundedSkeletonSubsequenceCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped _root_.Topology

/-- Countable bounded compactness plus identification of every selected
pointwise limit proves convergence of the entire sequence at every point. -/
theorem bounded_countable_unique_limit_tendsto_completion
    {Point : Type*} [Countable Point] (potentials : ℕ → Point → ℝ) (bound : ℝ)
    (bounded : ∀ index point, |potentials index point| ≤ bound) (target : Point → ℝ)
    (unique : ∀ selected : ℕ → ℕ, StrictMono selected → ∀ candidate : Point → ℝ,
      (∀ point, Tendsto (fun index => potentials (selected index) point) atTop (𝓝 (candidate point))) →
      candidate = target) :
    ∀ point, Tendsto (fun index => potentials index point) atTop (𝓝 (target point)) := by
  intro point
  apply Metric.tendsto_nhds.mpr
  intro epsilon epsilonPositive
  by_contra failure
  have frequent : ∃ᶠ index in atTop, epsilon ≤ dist (potentials index point) (target point) := by
    simpa only [Filter.Frequently, not_le] using failure
  obtain ⟨outer, outerStrict, far⟩ := extraction_of_frequently_atTop frequent
  obtain ⟨candidate, inner, innerStrict, _, convergence⟩ :=
    bounded_countable_potentials_subsequence_completion (fun index => potentials (outer index)) bound
      (fun index position => bounded (outer index) position)
  have identified := unique (outer ∘ inner) (outerStrict.comp innerStrict) candidate convergence
  subst candidate
  have distanceZero : Tendsto (fun index => dist (potentials (outer (inner index)) point) (target point)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [dist_self] using (convergence point).dist (tendsto_const_nhds (x := target point))
  have belowZero : epsilon ≤ 0 := le_of_tendsto_of_tendsto (tendsto_const_nhds (x := epsilon)) distanceZero
    (Eventually.of_forall fun index => far (inner index))
  linarith

end
end IGSIII34.Diffusion
