import Universality.Percolation.InternalMassPositiveLocalLimit

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

/-- The rescaled LLT error is exactly radius times the original error. -/
theorem local_limit_depth_shift_error (radius : ℝ) (hradius : 0 < radius)
    (probability : ℕ → ℤ → ℝ) (density : ℝ → ℝ) (n : ℕ) (size : ℤ) :
    |radius ^ (n + 1) * probability n size -
        radius * density (radius * ((size : ℝ) / radius ^ (n + 1)))| =
      radius * |radius ^ n * probability n size - density ((size : ℝ) / radius ^ n)| := by
  have hargument : radius * ((size : ℝ) / radius ^ (n + 1)) = (size : ℝ) / radius ^ n := by
    rw [pow_succ]
    field_simp [hradius.ne']
  rw [hargument, pow_succ]
  have heq : radius ^ n * radius * probability n size - radius * density ((size : ℝ) / radius ^ n) =
      radius * (radius ^ n * probability n size - density ((size : ℝ) / radius ^ n)) := by ring
  rw [heq, abs_mul, abs_of_pos hradius]

/-- Changing the scale from ρ^n to ρ^(n+1) changes the limiting density
exactly to x ↦ ρ w(ρx). -/
theorem uniform_local_limit_depth_shift (radius : ℝ) (hradius : 0 < radius)
    (probability : ℕ → ℤ → ℝ) (density : ℝ → ℝ)
    (hlimit : ∀ error, 0 < error → ∀ᶠ n : ℕ in atTop, ∀ size : ℤ,
      |radius ^ n * probability n size - density ((size : ℝ) / radius ^ n)| < error) :
    ∀ error, 0 < error → ∀ᶠ n : ℕ in atTop, ∀ size : ℤ,
      |radius ^ (n + 1) * probability n size -
        radius * density (radius * ((size : ℝ) / radius ^ (n + 1)))| < error := by
  intro error herror
  filter_upwards [hlimit (error / radius) (div_pos herror hradius)] with n hn
  intro size
  have hargument : radius * ((size : ℝ) / radius ^ (n + 1)) = (size : ℝ) / radius ^ n := by
    rw [pow_succ]
    field_simp [hradius.ne']
  rw [hargument, pow_succ]
  have heq : radius ^ n * radius * probability n size - radius * density ((size : ℝ) / radius ^ n) =
      radius * (radius ^ n * probability n size - density ((size : ℝ) / radius ^ n)) := by ring
  rw [heq, abs_mul, abs_of_pos hradius]
  simpa only [mul_comm] using (lt_div_iff₀ hradius).mp (hn size)

theorem depth_shift_density_properties (radius : ℝ) (hradius : 0 < radius)
    (density : ℝ → ℝ) (hsmooth : ContDiff ℝ ∞ density)
    (hnonnegative : ∀ x, 0 ≤ density x) (hintegrable : Integrable density)
    (hintegral : (∫ x, density x) = 1)
    (hnegative : ∀ x, x < 0 → density x = 0) :
    ContDiff ℝ ∞ (fun x => radius * density (radius * x)) ∧
    (∀ x, 0 ≤ radius * density (radius * x)) ∧
    Integrable (fun x => radius * density (radius * x)) ∧
    (∫ x, radius * density (radius * x)) = 1 ∧
    (∀ x, x < 0 → radius * density (radius * x) = 0) := by
  refine ⟨contDiff_const.mul (hsmooth.comp (contDiff_const.mul contDiff_id)),
    fun x => mul_nonneg hradius.le (hnonnegative _),
    (hintegrable.comp_mul_left' hradius.ne').const_mul radius, ?_, ?_⟩
  · rw [integral_const_mul, Measure.integral_comp_mul_left, hintegral,
      smul_eq_mul, abs_of_pos (inv_pos.mpr hradius), mul_one, mul_inv_cancel₀ hradius.ne']
  · intro x hx
    rw [hnegative _ (mul_neg_of_pos_of_neg hradius hx), mul_zero]

end
end Universality
