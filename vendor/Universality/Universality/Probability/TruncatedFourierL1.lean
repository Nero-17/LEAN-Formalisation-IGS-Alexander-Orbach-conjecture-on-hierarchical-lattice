import Universality.Probability.FourierL1Dominated

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem truncated_fourier_L1_convergence
    (finite : ℕ → ℝ → ℂ) (limit : ℝ → ℂ) (radius constant : ℝ)
    (hradius : 1 < radius) (hconstant : 0 ≤ constant)
    (hfinite : ∀ n, AEStronglyMeasurable (finite n))
    (hlimit : AEStronglyMeasurable limit)
    (hconvergence : ∀ t, Tendsto (fun n => finite n t) atTop (𝓝 (limit t)))
    (hnorm : ∀ n t, ‖finite n t‖ ≤ 1)
    (hquadratic : ∀ᶠ n : ℕ in atTop, ∀ t,
      1 ≤ |t| → |t| ≤ Real.pi * radius ^ n → ‖finite n t‖ * |t| ^ 2 ≤ constant) :
    Integrable limit ∧
      Tendsto (fun n => ∫ t : ℝ,
        ‖(Set.Ioc (-Real.pi * radius ^ n) (Real.pi * radius ^ n)).indicator (finite n) t - limit t‖)
        atTop (𝓝 0) := by
  classical
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  apply Fourier_L1_convergence_of_polynomial_two _ limit constant hconstant
    (fun n => (hfinite n).indicator measurableSet_Ioc) hlimit
  · intro t
    have hlarge : ∀ᶠ n : ℕ in atTop, |t| + 1 ≤ radius ^ n :=
      (tendsto_pow_atTop_atTop_of_one_lt hradius).eventually (eventually_ge_atTop (|t| + 1))
    apply (hconvergence t).congr'
    filter_upwards [hlarge] with n hn
    have hmember : t ∈ Set.Ioc (-Real.pi * radius ^ n) (Real.pi * radius ^ n) := by
      have hp := pow_pos hradius0 n
      have hpi := Real.two_le_pi
      constructor <;> nlinarith [le_abs_self t, neg_abs_le t]
    exact (Set.indicator_of_mem hmember (finite n)).symm
  · filter_upwards [hquadratic] with n hn
    intro t
    by_cases hmember : t ∈ Set.Ioc (-Real.pi * radius ^ n) (Real.pi * radius ^ n)
    · rw [Set.indicator_of_mem hmember]
      refine ⟨hnorm n t, fun ht => hn t ht ?_⟩
      apply abs_le.mpr
      constructor
      · have := hmember.1.le
        linarith
      · exact hmember.2
    · rw [Set.indicator_of_notMem hmember]
      simp only [norm_zero, zero_le_one, zero_mul, hconstant, implies_true, and_self]

end
end Universality
