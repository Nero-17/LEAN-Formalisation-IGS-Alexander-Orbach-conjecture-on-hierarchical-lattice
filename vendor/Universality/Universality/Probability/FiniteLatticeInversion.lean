import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

namespace Universality
noncomputable section
open MeasureTheory
open scoped BigOperators

theorem integral_integer_character (frequency : ℤ) :
    (∫ t in -Real.pi..Real.pi,
      Complex.exp ((frequency : ℂ) * Complex.I * (t : ℂ))) =
        if frequency = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hzero : frequency = 0
  · simp [hzero, intervalIntegral.integral_const, sub_neg_eq_add, two_mul]
  · rw [if_neg hzero, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hzero) Complex.I_ne_zero)]
    have hperiod : Complex.exp ((frequency : ℂ) * Complex.I * (Real.pi : ℂ)) =
        Complex.exp ((frequency : ℂ) * Complex.I * (-Real.pi : ℂ)) := by
      calc
        _ = Complex.exp (((frequency : ℂ) * Complex.I * (-Real.pi : ℂ)) +
            (frequency : ℂ) * (2 * Real.pi * Complex.I)) := by congr 1 <;> ring
        _ = _ := by rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [Complex.ofReal_neg, hperiod, sub_self, zero_div]

theorem finite_lattice_fourier_inversion {index : Type*} [Fintype index]
    (weight : index → ℂ) (mass : index → ℕ) (size : ℕ) :
    (∫ t in -Real.pi..Real.pi,
      (∑ i, weight i * Complex.exp ((t : ℂ) * (mass i : ℂ) * Complex.I)) *
        Complex.exp (-(t : ℂ) * (size : ℂ) * Complex.I)) =
      (2 * Real.pi : ℂ) * ∑ i, if mass i = size then weight i else 0 := by
  have hexp (i : index) (t : ℝ) :
      weight i * Complex.exp ((t : ℂ) * (mass i : ℂ) * Complex.I) *
        Complex.exp (-(t : ℂ) * (size : ℂ) * Complex.I) =
      weight i * Complex.exp ((((mass i : ℤ) - (size : ℤ) : ℤ) : ℂ) * Complex.I * (t : ℂ)) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [Finset.sum_mul, hexp]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_integer_character]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases heq : mass i = size
    · simp [heq, mul_comm]
    · have hne : (mass i : ℤ) - (size : ℤ) ≠ 0 := by omega
      simp [hne, heq]
  · intro i hi
    exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem scaled_finite_lattice_fourier_inversion {index : Type*} [Fintype index]
    (weight : index → ℂ) (mass : index → ℕ) (size : ℕ)
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ t in -Real.pi * scale..Real.pi * scale,
      (∑ i, weight i * Complex.exp (((t / scale : ℝ) : ℂ) * (mass i : ℂ) * Complex.I)) *
        Complex.exp (-((t / scale : ℝ) : ℂ) * (size : ℂ) * Complex.I)) =
      (scale : ℂ) * (2 * Real.pi : ℂ) * ∑ i, if mass i = size then weight i else 0 := by
  rw [intervalIntegral.integral_comp_div
    (fun t : ℝ => (∑ i, weight i * Complex.exp ((t : ℂ) * (mass i : ℂ) * Complex.I)) *
      Complex.exp (-(t : ℂ) * (size : ℂ) * Complex.I)) hscale.ne']
  simp only [mul_div_cancel_right₀ _ hscale.ne']
  rw [finite_lattice_fourier_inversion]
  simp only [Complex.real_smul]
  ring

end
end Universality
