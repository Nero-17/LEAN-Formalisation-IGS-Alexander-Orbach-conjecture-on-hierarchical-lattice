import Universality.Probability.FiniteLatticeInversion
import Universality.Probability.InverseCharacteristic

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

def truncatedLatticeCharacteristic {index : Type*} [Fintype index]
    (weight : index → ℂ) (mass : index → ℕ) (scale : ℝ) : ℝ → ℂ :=
  (Set.Ioc (-Real.pi * scale) (Real.pi * scale)).indicator (fun t =>
    ∑ i, weight i * Complex.exp (((t / scale : ℝ) : ℂ) * (mass i : ℂ) * Complex.I))

theorem integrable_truncatedLatticeCharacteristic {index : Type*} [Fintype index]
    (weight : index → ℂ) (mass : index → ℕ) (scale : ℝ) :
    Integrable (truncatedLatticeCharacteristic weight mass scale) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  apply Continuous.integrableOn_Ioc
  fun_prop

theorem inverse_truncatedLatticeCharacteristic {index : Type*} [Fintype index]
    (weight : index → ℂ) (mass : index → ℕ) (size : ℕ)
    (scale : ℝ) (hscale : 0 < scale) :
    inverseCharacteristic (truncatedLatticeCharacteristic weight mass scale)
        ((size : ℝ) / scale) =
      (scale : ℂ) * ∑ i, if mass i = size then weight i else 0 := by
  unfold inverseCharacteristic truncatedLatticeCharacteristic
  simp_rw [← Set.indicator_mul_right _
    (fun t : ℝ => Complex.exp (-(t * ((size : ℝ) / scale) : ℝ) * Complex.I))]
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le
      (by nlinarith [mul_pos Real.pi_pos hscale] : -Real.pi * scale ≤ Real.pi * scale)]
  have hkernel (t : ℝ) :
      Complex.exp (-(t * ((size : ℝ) / scale) : ℝ) * Complex.I) *
          (∑ i, weight i * Complex.exp (((t / scale : ℝ) : ℂ) * (mass i : ℂ) * Complex.I)) =
        (∑ i, weight i * Complex.exp (((t / scale : ℝ) : ℂ) * (mass i : ℂ) * Complex.I)) *
          Complex.exp (-((t / scale : ℝ) : ℂ) * (size : ℂ) * Complex.I) := by
    rw [mul_comm]
    congr 2
    push_cast
    ring
  simp_rw [hkernel]
  rw [scaled_finite_lattice_fourier_inversion weight mass size scale hscale]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  field_simp

theorem lattice_local_limit_of_L1 (index : ℕ → Type*) [∀ n, Fintype (index n)]
    (weight : ∀ n, index n → ℂ) (mass : ∀ n, index n → ℕ)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (limit : ℝ → ℂ) (hlimit : Integrable limit)
    (hconvergence : Tendsto (fun n => ∫ t : ℝ,
      ‖truncatedLatticeCharacteristic (weight n) (mass n) (scale n) t - limit t‖)
      atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ size : ℕ,
      ‖(scale n : ℂ) * (∑ i, if mass n i = size then weight n i else 0) -
        inverseCharacteristic limit ((size : ℝ) / scale n)‖ < ε := by
  have huniform := inverseCharacteristic_uniform_of_L1
    (fun n => truncatedLatticeCharacteristic (weight n) (mass n) (scale n)) limit
    (fun n => integrable_truncatedLatticeCharacteristic (weight n) (mass n) (scale n)) hlimit hconvergence
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp huniform) ε hε] with n hn
  intro size
  have hvalue := hn ((size : ℝ) / scale n)
  rw [dist_comm, dist_eq_norm, inverse_truncatedLatticeCharacteristic
    (weight n) (mass n) size (scale n) (hscale n)] at hvalue
  exact hvalue

end
end Universality
