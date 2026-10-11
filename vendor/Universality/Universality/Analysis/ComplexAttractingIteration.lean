import Universality.Analysis.ComplexDiscountedBasin
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Universality
noncomputable section
open Filter Set Metric
open scoped Topology

/-- A zero-derivative complex fixed point has an invariant open ball. -/
theorem complex_zero_derivative_invariant_ball (iteration : ℂ → ℂ) (fixed : ℂ)
    (hfixed : iteration fixed = fixed) (hderivative : HasDerivAt iteration 0 fixed) :
    ∃ radius : ℝ, 0 < radius ∧ MapsTo iteration (ball fixed radius) (ball fixed radius) := by
  have hsmall := hderivative.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  simp only [hfixed, smul_zero, sub_zero] at hsmall
  obtain ⟨radius, hradius, hball⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨radius, hradius, ?_⟩
  intro point hpoint
  have h := hball (y := point) hpoint
  change dist (iteration point) fixed < radius
  simp only [Metric.mem_ball, dist_eq_norm] at hpoint ⊢
  linarith

/-- Every point whose orbit converges to a superattracting fixed point has a
genuine holomorphic neighborhood for the full discounted orbit series. -/
theorem complexDiscountedIteration_analyticAt_of_attracted
    (iteration forcing : ℂ → ℂ) (discount point fixed : ℂ)
    (hdiscount : ‖discount‖ < 1)
    (hiteration : Differentiable ℂ iteration) (hforcing : Differentiable ℂ forcing)
    (hfixed : iteration fixed = fixed) (hderivative : HasDerivAt iteration 0 fixed)
    (horbit : Tendsto (fun n : ℕ => iteration^[n] point) atTop (𝓝 fixed)) :
    AnalyticAt ℂ (complexDiscountedIteration iteration forcing discount) point := by
  obtain ⟨radius, hradius, hmaps⟩ :=
    complex_zero_derivative_invariant_ball iteration fixed hfixed hderivative
  obtain ⟨bound, hbound⟩ := (isCompact_closedBall fixed radius).exists_bound_of_continuousOn
    hforcing.continuous.continuousOn
  obtain ⟨depth, hdepth⟩ := (horbit.eventually (ball_mem_nhds fixed hradius)).exists
  exact complexDiscountedIteration_analyticAt_of_enters iteration forcing discount
    (ball fixed radius) bound hdiscount isOpen_ball hiteration hforcing hmaps
    (fun point hp => hbound point (mem_closedBall.mpr (mem_ball.mp hp).le)) point depth hdepth

end
end Universality
