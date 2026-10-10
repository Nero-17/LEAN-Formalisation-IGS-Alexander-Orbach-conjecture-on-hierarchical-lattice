import Universality.Probability.InverseCharacteristicFourier
import Mathlib.Analysis.Fourier.Inversion

namespace Universality
noncomputable section
open MeasureTheory
open scoped FourierTransform

theorem integrable_fourier_of_inverseCharacteristic {function : ℝ → ℂ}
    (h : Integrable (inverseCharacteristic function)) : Integrable (𝓕 function) := by
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have heq (x : ℝ) : (𝓕 function) x =
      (2 * Real.pi : ℂ) * inverseCharacteristic function (2 * Real.pi * x) := by
    rw [inverseCharacteristic_eq_fourier]
    have hx : 2 * Real.pi * x / (2 * Real.pi) = x := by field_simp
    rw [hx]
    simp [← mul_assoc, Real.pi_ne_zero]
  exact ((h.comp_mul_left' hscale).const_mul (2 * Real.pi : ℂ)).congr
    (Filter.Eventually.of_forall fun x => (heq x).symm)

theorem integral_exp_mul_inverseCharacteristic {function : ℝ → ℂ}
    (hintegrable : Integrable function) (hinverse : Integrable (inverseCharacteristic function))
    (hcontinuous : Continuous function) (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) * inverseCharacteristic function x) =
      function t := by
  have hscale : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hinversion := hintegrable.fourierInv_fourier_eq
    (integrable_fourier_of_inverseCharacteristic hinverse) (hcontinuous.continuousAt (x := t))
  rw [Real.fourierInv_eq'] at hinversion
  let integrand : ℝ → ℂ := fun x => Complex.exp ((2 * Real.pi * (x * t) : ℝ) * Complex.I) * (𝓕 function) x
  have hintegrand : (∫ x : ℝ, integrand x) = function t := by
    simpa [integrand, mul_comm] using hinversion
  calc
    _ = (2 * Real.pi : ℂ)⁻¹ * ∫ x : ℝ, integrand (x / (2 * Real.pi)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [inverseCharacteristic_eq_fourier]
        dsimp only [integrand]
        have hphase : 2 * Real.pi * (x / (2 * Real.pi) * t) = t * x := by
          field_simp
        rw [hphase]
        ring
    _ = (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℝ) • function t) := by
      rw [Measure.integral_comp_div, abs_of_pos hscale, hintegrand]
    _ = function t := by
      rw [Complex.real_smul]
      push_cast
      field_simp

end
end Universality
