import Universality.Probability.L2Characteristic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem quadratic_fourier_domination (value : ℂ) (frequency constant : ℝ)
    (hconstant : 0 ≤ constant) (hnorm : ‖value‖ ≤ 1)
    (hquadratic : 1 ≤ |frequency| → ‖value‖ * |frequency| ^ 2 ≤ constant) :
    ‖value‖ ≤ (constant + 2) * (1 + frequency ^ 2)⁻¹ := by
  have hdenominator : 0 < 1 + frequency ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hdenominator]
  by_cases hlarge : 1 ≤ |frequency|
  · have hbound := hquadratic hlarge
    rw [sq_abs] at hbound
    nlinarith
  · have hsquare : frequency ^ 2 ≤ 1 := by
      have := (sq_le_sq₀ (abs_nonneg frequency) (by norm_num : (0 : ℝ) ≤ 1)).mpr
        (le_of_lt (lt_of_not_ge hlarge))
      simpa only [sq_abs, one_pow] using this
    nlinarith [norm_nonneg value]

/-- An eventual quadratic Fourier envelope gives integrability of the limit
and convergence in L1, including for truncated lattice characteristic functions. -/
theorem Fourier_L1_convergence_of_polynomial_two
    (finite : ℕ → ℝ → ℂ) (limit : ℝ → ℂ) (constant : ℝ)
    (hconstant : 0 ≤ constant)
    (hfinite : ∀ n, AEStronglyMeasurable (finite n))
    (hlimit : AEStronglyMeasurable limit)
    (hconvergence : ∀ t, Tendsto (fun n => finite n t) atTop (𝓝 (limit t)))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ t, ‖finite n t‖ ≤ 1 ∧
      (1 ≤ |t| → ‖finite n t‖ * |t| ^ 2 ≤ constant)) :
    Integrable limit ∧
      Tendsto (fun n => ∫ t : ℝ, ‖finite n t - limit t‖) atTop (𝓝 0) := by
  let envelope (t : ℝ) := (constant + 2) * (1 + t ^ 2)⁻¹
  have henvelope : Integrable envelope := integrable_inv_one_add_sq.const_mul _
  have hfiniteBound : ∀ᶠ n : ℕ in atTop, ∀ t, ‖finite n t‖ ≤ envelope t := by
    filter_upwards [hbound] with n hn
    intro t
    exact quadratic_fourier_domination _ t constant hconstant (hn t).1 (hn t).2
  have hlimitBound (t : ℝ) : ‖limit t‖ ≤ envelope t :=
    le_of_tendsto (hconvergence t).norm (hfiniteBound.mono (fun n hn => hn t))
  have hlimitIntegrable : Integrable limit :=
    henvelope.mono' hlimit (Eventually.of_forall hlimitBound)
  refine ⟨hlimitIntegrable, ?_⟩
  have hdominated := tendsto_integral_filter_of_dominated_convergence
    (F := fun n t => ‖finite n t - limit t‖) (f := fun _ : ℝ => (0 : ℝ))
    (fun t => 2 * envelope t)
    (Eventually.of_forall (fun n => ((hfinite n).sub hlimit).norm))
    (hfiniteBound.mono (fun n hn => Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by linarith [hn t, hlimitBound t]))))
    (henvelope.const_mul 2)
    (Eventually.of_forall (fun t => by simpa using ((hconvergence t).sub_const (limit t)).norm))
  simpa only [integral_zero] using hdominated

end
end Universality
