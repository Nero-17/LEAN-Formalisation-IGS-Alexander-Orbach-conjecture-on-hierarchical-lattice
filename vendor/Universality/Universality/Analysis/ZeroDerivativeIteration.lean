import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace Universality
noncomputable section
open Filter
open scoped Topology

/-- An orbit converging to a fixed point with zero derivative beats every
prescribed geometric weight in an absolutely convergent series. -/
theorem summable_weighted_iterate_sub_of_derivative_zero
    (map : ℝ → ℝ) (start fixed growth : ℝ) (hgrowth : 0 < growth)
    (hfixed : map fixed = fixed) (hderivative : HasDerivAt map 0 fixed)
    (hlimit : Tendsto (fun n : ℕ => map^[n] start) atTop (𝓝 fixed)) :
    Summable (fun n : ℕ => growth ^ n * (map^[n] start - fixed)) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  have hsmall := hderivative.isLittleO.bound (show 0 < 1 / (2 * growth) by positivity)
  filter_upwards [hlimit.eventually hsmall] with n hn
  simp only [hfixed, smul_zero, sub_zero, ← Function.iterate_succ_apply'] at hn
  simp only [norm_mul, Real.norm_of_nonneg (pow_nonneg hgrowth.le _),
    Real.norm_of_nonneg hgrowth.le, pow_succ]
  calc
    growth ^ n * growth * ‖map^[n + 1] start - fixed‖ ≤
        growth ^ n * growth * ((1 / (2 * growth)) * ‖map^[n] start - fixed‖) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (pow_nonneg hgrowth.le _) hgrowth.le)
    _ = (1 / 2) * (growth ^ n * ‖map^[n] start - fixed‖) := by
      field_simp [hgrowth.ne']

end
end Universality
