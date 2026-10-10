import Universality.Analysis.FiniteEscapeEstimate
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Universality
noncomputable section
set_option maxHeartbeats 0
open Polynomial Filter
open scoped Topology

theorem polynomial_secant_factor (polynomial : Polynomial ℝ) (center : ℝ) :
    ∃ quotient : Polynomial ℝ,
      (∀ point, polynomial.eval point - polynomial.eval center = (point - center) * quotient.eval point) ∧
      quotient.eval center = polynomial.derivative.eval center := by
  obtain ⟨quotient, hfactor⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := polynomial) (a := center)
  refine ⟨quotient, ?_, ?_⟩
  · intro point
    have h := congrArg (Polynomial.eval point) hfactor
    simpa only [eval_sub, eval_C, eval_mul, eval_X] using h
  · have h := congrArg (fun p : Polynomial ℝ => p.derivative.eval center) hfactor
    simpa only [derivative_sub, derivative_C, sub_zero, derivative_mul, derivative_X,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one, sub_self, zero_mul, add_zero, one_mul] using h.symm

/-- A repelling polynomial fixed point has a positive secant bounded away
from one, and its logarithm differs from the log multiplier by a linear error. -/
theorem polynomial_secant_local_bounds (polynomial : Polynomial ℝ) (center : ℝ)
    (hrepelling : 1 < polynomial.derivative.eval center) :
    ∃ quotient : Polynomial ℝ, ∃ lower upper rate : ℝ,
      1 < lower ∧ 0 < rate ∧
      (∀ point, polynomial.eval point - polynomial.eval center = (point - center) * quotient.eval point) ∧
      ∀ᶠ point in 𝓝 center,
        lower ≤ quotient.eval point ∧ quotient.eval point ≤ upper ∧
          |Real.log (quotient.eval point) - Real.log (polynomial.derivative.eval center)| ≤ rate * |point - center| := by
  obtain ⟨quotient, hfactor, hvalue⟩ := polynomial_secant_factor polynomial center
  have hpositive : 0 < quotient.eval center := by rw [hvalue]; linarith
  obtain ⟨rate, hrate, hbound⟩ := ((quotient.hasDerivAt center).log hpositive.ne').isBigO_sub.exists_pos
  have hcontinuity := (quotient.hasDerivAt center).continuousAt
  have hlower := hcontinuity.eventually (lt_mem_nhds (show
    (polynomial.derivative.eval center + 1) / 2 < quotient.eval center by rw [hvalue]; linarith))
  have hupper := hcontinuity.eventually (gt_mem_nhds (show
    quotient.eval center < polynomial.derivative.eval center + 1 by rw [hvalue]; linarith))
  refine ⟨quotient, (polynomial.derivative.eval center + 1) / 2,
    polynomial.derivative.eval center + 1, rate, by linarith, hrate, hfactor, ?_⟩
  filter_upwards [hlower, hupper, hbound.bound] with point hl hu hb
  refine ⟨hl.le, hu.le, ?_⟩
  simpa only [Real.norm_eq_abs, hvalue] using hb

end
end Universality
