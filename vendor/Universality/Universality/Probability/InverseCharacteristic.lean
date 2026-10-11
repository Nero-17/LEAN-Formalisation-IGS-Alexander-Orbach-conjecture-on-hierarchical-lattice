import Universality.Probability.L2Characteristic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology

def inverseCharacteristic (characteristic : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ,
    Complex.exp (-(t * x : ℝ) * Complex.I) * characteristic t

theorem integrable_inverse_characteristic_kernel {characteristic : ℝ → ℂ}
    (h : Integrable characteristic) (x : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-(t * x : ℝ) * Complex.I) * characteristic t) := by
  apply h.bdd_mul (c := 1) (by fun_prop)
  exact Eventually.of_forall (fun t => by simp [Complex.norm_exp])

theorem inverseCharacteristic_sub_bound {first second : ℝ → ℂ}
    (hfirst : Integrable first) (hsecond : Integrable second) (x : ℝ) :
    ‖inverseCharacteristic first x - inverseCharacteristic second x‖ ≤
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖first t - second t‖ := by
  unfold inverseCharacteristic
  rw [← mul_sub, ← integral_sub (integrable_inverse_characteristic_kernel hfirst x)
    (integrable_inverse_characteristic_kernel hsecond x)]
  simp_rw [← mul_sub]
  rw [norm_mul]
  have hnorm : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∫ t : ℝ, ‖Complex.exp (-(t * x : ℝ) * Complex.I) * (first t - second t)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp [norm_mul, Complex.norm_exp]

theorem continuous_inverseCharacteristic {characteristic : ℝ → ℂ}
    (h : Integrable characteristic) : Continuous (inverseCharacteristic characteristic) := by
  apply continuous_const.mul
  apply continuous_of_dominated (bound := fun t => ‖characteristic t‖)
  · exact fun x => (integrable_inverse_characteristic_kernel h x).1
  · exact fun x => Eventually.of_forall (fun t => by simp [norm_mul, Complex.norm_exp])
  · exact h.norm
  · exact Eventually.of_forall (fun t => by fun_prop)

theorem inverseCharacteristic_uniform_of_L1 (characteristic : ℕ → ℝ → ℂ)
    (limit : ℝ → ℂ) (hcharacteristic : ∀ n, Integrable (characteristic n))
    (hlimit : Integrable limit)
    (hconvergence : Tendsto (fun n => ∫ t : ℝ, ‖characteristic n t - limit t‖)
      atTop (𝓝 0)) :
    TendstoUniformly (fun n => inverseCharacteristic (characteristic n))
      (inverseCharacteristic limit) atTop := by
  have hscaled : Tendsto (fun n => (2 * Real.pi)⁻¹ *
      ∫ t : ℝ, ‖characteristic n t - limit t‖) atTop (𝓝 0) := by
    simpa using hconvergence.const_mul (2 * Real.pi)⁻¹
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hscaled.eventually (gt_mem_nhds hε)] with n hn
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (inverseCharacteristic_sub_bound (hcharacteristic n) hlimit x).trans_lt hn

end
end Universality
