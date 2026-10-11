import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace Universality
noncomputable section
open Filter Set
open scoped Topology

/-- A continuous function whose punctured derivative has a finite limit is
really differentiable at the missing point. This is the step needed after
renormalization estimates; a Taylor or Peano remainder alone is not used. -/
theorem hasDerivAt_of_punctured_derivative_limit (function derivative : ℝ → ℝ)
    (center value : ℝ) (hcontinuous : ContinuousAt function center)
    (hderivative : ∀ᶠ point in 𝓝[≠] center, HasDerivAt function (derivative point) point)
    (hlimit : Tendsto derivative (𝓝[≠] center) (𝓝 value)) :
    HasDerivAt function value center := by
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field]
  apply HasDerivAt.lhopital_zero_nhdsNE
    (hderivative.mono (fun point hp => hp.sub_const (function center)))
    (Eventually.of_forall (fun point => (hasDerivAt_id point).sub_const center))
    (Eventually.of_forall (fun _ => one_ne_zero))
  · simpa only [sub_self] using
      (hcontinuous.tendsto.mono_left nhdsWithin_le_nhds).sub_const (function center)
  · simpa only [sub_self] using
      ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 center) (𝓝 center)).mono_left
        nhdsWithin_le_nhds).sub_const center
  · simpa only [div_one] using hlimit

theorem contDiffAt_succ_of_deriv (function : ℝ → ℝ) (center : ℝ) (order : ℕ)
    (hdifferentiable : ∀ᶠ point in 𝓝 center, DifferentiableAt ℝ function point)
    (hderivative : ContDiffAt ℝ order (deriv function) center) :
    ContDiffAt ℝ (order + 1) function center := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun point => (1 : ℝ →L[ℝ] ℝ).smulRight (deriv function point), ?_,
    contDiffAt_const.smulRight hderivative⟩
  exact ⟨{point | DifferentiableAt ℝ function point}, hdifferentiable,
    fun point hp => hp.hasDerivAt.hasFDerivAt⟩

end
end Universality

