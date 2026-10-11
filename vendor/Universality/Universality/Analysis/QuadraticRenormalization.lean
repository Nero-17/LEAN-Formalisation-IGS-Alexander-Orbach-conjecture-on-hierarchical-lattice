import Universality.Analysis.PolynomialEscapeBounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Polynomial

namespace Universality
noncomputable section
open Filter Polynomial
open scoped Topology

/-- Two exact secant factorizations give a uniform quadratic Taylor remainder
for a real polynomial on the unit interval. -/
theorem polynomial_quadratic_remainder_bound (polynomial : Polynomial ℝ) (center : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ point ∈ Set.Icc (0 : ℝ) 1,
      |polynomial.eval point - polynomial.eval center -
        polynomial.derivative.eval center * (point - center)| ≤ bound * (point - center) ^ 2 := by
  obtain ⟨firstQuotient, hfirst, hvalue⟩ := polynomial_secant_factor polynomial center
  obtain ⟨secondQuotient, hsecond, _⟩ := polynomial_secant_factor firstQuotient center
  obtain ⟨bound, hbound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (secondQuotient.continuous.continuousOn : ContinuousOn secondQuotient.eval (Set.Icc (0 : ℝ) 1))
  have hnonnegative : 0 ≤ bound := (norm_nonneg _).trans (hbound 0 (by norm_num))
  refine ⟨bound, hnonnegative, ?_⟩
  intro point hpoint
  have hid : polynomial.eval point - polynomial.eval center -
      polynomial.derivative.eval center * (point - center) =
      (point - center) ^ 2 * secondQuotient.eval point := by
    rw [hfirst, ← hvalue]
    linear_combination (point - center) * hsecond point
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simpa only [Real.norm_eq_abs, mul_comm] using
    mul_le_mul_of_nonneg_left (hbound point hpoint) (sq_nonneg (point - center))

/-- Backward propagation of a quadratic bound from an orbit's exit point.
This uses a true bounded renormalization solution, not assumed regularity. -/
theorem quadratic_bound_from_finite_exit {space : Type*}
    (iteration : space → space) (remainder deviation : space → ℝ)
    (mass expansion forcing bound radius : ℝ)
    (hmass : 0 < mass) (hexpansion : 0 ≤ expansion) (hbound : 0 ≤ bound)
    (hbalance : forcing + bound * expansion ^ 2 ≤ mass * bound)
    (houtside : ∀ point, radius ≤ |deviation point| →
      |remainder point| ≤ bound * deviation point ^ 2)
    (hstep : ∀ point, |deviation point| < radius →
      |deviation (iteration point)| ≤ expansion * |deviation point|)
    (hequation : ∀ point, |deviation point| < radius →
      |mass * remainder point - remainder (iteration point)| ≤ forcing * deviation point ^ 2)
    (point : space) (depth : ℕ) (hexit : radius ≤ |deviation (iteration^[depth] point)|) :
    |remainder point| ≤ bound * deviation point ^ 2 := by
  induction depth generalizing point with
  | zero => exact houtside point (by simpa using hexit)
  | succ depth ih =>
    by_cases hout : radius ≤ |deviation point|
    · exact houtside point hout
    have hinside := lt_of_not_ge hout
    have hnext : |remainder (iteration point)| ≤ bound * deviation (iteration point) ^ 2 :=
      ih (iteration point) (by simpa only [Function.iterate_succ_apply] using hexit)
    have hsquare : deviation (iteration point) ^ 2 ≤ expansion ^ 2 * deviation point ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (deviation (iteration point))) (hstep point hinside) 2
      simpa only [sq_abs, mul_pow] using h
    apply (mul_le_mul_iff_right₀ hmass).mp
    calc
      mass * |remainder point| = |mass * remainder point| := by
        rw [abs_mul, abs_of_pos hmass]
      _ ≤ |mass * remainder point - remainder (iteration point)| +
          |remainder (iteration point)| := by
        have h := abs_add_le (mass * remainder point - remainder (iteration point))
          (remainder (iteration point))
        simpa only [sub_add_cancel] using h
      _ ≤ forcing * deviation point ^ 2 + bound * deviation (iteration point) ^ 2 :=
        add_le_add (hequation point hinside) hnext
      _ ≤ forcing * deviation point ^ 2 + bound * (expansion ^ 2 * deviation point ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsquare hbound)
      _ = (forcing + bound * expansion ^ 2) * deviation point ^ 2 := by ring
      _ ≤ (mass * bound) * deviation point ^ 2 :=
        mul_le_mul_of_nonneg_right hbalance (sq_nonneg _)
      _ = mass * (bound * deviation point ^ 2) := by ring

theorem hasDerivAt_of_quadratic_remainder (density : ℝ → ℝ)
    (critical coefficient bound : ℝ)
    (hbound : ∀ᶠ p in 𝓝 critical,
      |density p - density critical - coefficient * (p - critical)| ≤ bound * (p - critical) ^ 2) :
    HasDerivAt density coefficient critical := by
  rw [hasDerivAt_iff_tendsto]
  have hmajorant : Tendsto (fun p : ℝ => bound * |p - critical|) (𝓝 critical) (𝓝 0) := by
    have h : Tendsto (fun p : ℝ => p - critical) (𝓝 critical) (𝓝 0) := by
      simpa using (tendsto_id.sub_const critical :
        Tendsto (fun p : ℝ => p - critical) (𝓝 critical) (𝓝 (critical - critical)))
    simpa using h.abs.const_mul bound
  apply squeeze_zero' (Eventually.of_forall (fun p => mul_nonneg (by positivity) (norm_nonneg _)))
    _ hmajorant
  filter_upwards [hbound] with p hp
  simp only [Real.norm_eq_abs, smul_eq_mul]
  rw [mul_comm (p - critical) coefficient]
  calc
    _ ≤ |p - critical|⁻¹ * (bound * (p - critical) ^ 2) :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (abs_nonneg _))
    _ = bound * |p - critical| := by
      by_cases heq : p - critical = 0
      · simp [heq]
      have hne : |p - critical| ≠ 0 := abs_ne_zero.mpr heq
      rw [← sq_abs (p - critical)]
      field_simp
      <;> ring

end
end Universality
