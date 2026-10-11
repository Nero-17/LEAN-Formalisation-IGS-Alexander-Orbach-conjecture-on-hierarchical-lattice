import Universality.Probability.TruncatedFourierL1

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem norm_pow_le_norm_of_le_one (value : ℂ) (hvalue : ‖value‖ ≤ 1)
    (count : ℕ) (hcount : 1 ≤ count) : ‖value ^ count‖ ≤ ‖value‖ := by
  obtain ⟨previous, rfl⟩ : ∃ previous, count = previous + 1 := ⟨count - 1, by omega⟩
  rw [norm_pow, pow_succ]
  have hpower : ‖value‖ ^ previous ≤ 1 := pow_le_one₀ (norm_nonneg _) hvalue
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpower (norm_nonneg value)

/-- Adding one lattice vertex and summing a fixed positive number of independent copies
preserves the dominated Fourier local-limit mechanism. -/
theorem truncated_shifted_power_L1_convergence
    (finite : ℕ → ℝ → ℂ) (limit : ℝ → ℂ) (radius constant : ℝ)
    (hradius : 1 < radius) (hconstant : 0 ≤ constant)
    (hfinite : ∀ n, AEStronglyMeasurable (finite n))
    (hlimit : AEStronglyMeasurable limit)
    (hconvergence : ∀ t, Tendsto (fun n => finite n t) atTop (𝓝 (limit t)))
    (hnorm : ∀ n t, ‖finite n t‖ ≤ 1)
    (hquadratic : ∀ᶠ n : ℕ in atTop, ∀ t,
      1 ≤ |t| → |t| ≤ Real.pi * radius ^ n → ‖finite n t‖ * |t| ^ 2 ≤ constant)
    (count : ℕ) (hcount : 1 ≤ count) :
    Integrable (fun t => limit t ^ count) ∧
      Tendsto (fun n => ∫ t : ℝ,
        ‖(Set.Ioc (-Real.pi * radius ^ n) (Real.pi * radius ^ n)).indicator
          (fun t => Complex.exp (((t / radius ^ n : ℝ) : ℂ) * Complex.I) * finite n t ^ count) t -
            limit t ^ count‖) atTop (𝓝 0) := by
  apply truncated_fourier_L1_convergence
    (fun n t => Complex.exp (((t / radius ^ n : ℝ) : ℂ) * Complex.I) * finite n t ^ count)
    (fun t => limit t ^ count) radius constant hradius hconstant
  · intro n
    have hphase : Continuous (fun t : ℝ => Complex.exp (((t / radius ^ n : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact hphase.aestronglyMeasurable.mul ((hfinite n).pow count)
  · exact hlimit.pow count
  · intro t
    have hfrequency : Tendsto (fun n : ℕ => t / radius ^ n) atTop (𝓝 0) :=
      (tendsto_pow_atTop_atTop_of_one_lt hradius).const_div_atTop t
    have hcomplex := (Complex.continuous_ofReal.tendsto 0).comp hfrequency
    have hphase : Tendsto (fun n : ℕ => Complex.exp (((t / radius ^ n : ℝ) : ℂ) * Complex.I)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using
        (Complex.continuous_exp.tendsto _).comp (hcomplex.mul_const Complex.I)
    simpa only [one_mul] using hphase.mul ((hconvergence t).pow count)
  · intro n t
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hnorm n t)
  · filter_upwards [hquadratic] with n hn
    intro t ht ht'
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact (mul_le_mul_of_nonneg_right (norm_pow_le_norm_of_le_one (finite n t) (hnorm n t) count hcount)
      (sq_nonneg |t|)).trans (hn t ht ht')

end
end Universality

