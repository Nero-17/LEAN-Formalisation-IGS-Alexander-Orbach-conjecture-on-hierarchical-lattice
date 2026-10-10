import Universality.Probability.InverseCharacteristic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace Universality
noncomputable section
open MeasureTheory Real

def gaussianFourierKernel (width x : ℝ) : ℝ :=
  Real.sqrt (Real.pi / width) / (2 * Real.pi) * Real.exp (-(x ^ 2 / (4 * width)))

theorem gaussianFourierKernel_nonneg (width x : ℝ) : 0 ≤ gaussianFourierKernel width x := by
  unfold gaussianFourierKernel
  positivity

theorem integrable_gaussianFourierKernel (width : ℝ) (hwidth : 0 < width) :
    Integrable (gaussianFourierKernel width) := by
  convert (integrable_exp_neg_mul_sq (by positivity : 0 < (4 * width)⁻¹)).const_mul
    (Real.sqrt (Real.pi / width) / (2 * Real.pi)) using 1
  ext x
  unfold gaussianFourierKernel
  congr 2
  ring

theorem integral_gaussianFourierKernel (width : ℝ) (hwidth : 0 < width) :
    (∫ x : ℝ, gaussianFourierKernel width x) = 1 := by
  have hform (x : ℝ) : gaussianFourierKernel width x =
      Real.sqrt (Real.pi / width) / (2 * Real.pi) * Real.exp (-((4 * width)⁻¹) * x ^ 2) := by
    unfold gaussianFourierKernel
    congr 2
    ring
  simp_rw [hform]
  rw [integral_const_mul, integral_gaussian]
  have hproduct : Real.sqrt (Real.pi / width) * Real.sqrt (Real.pi / (4 * width)⁻¹) =
      2 * Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    have heq : Real.pi / width * (Real.pi / (4 * width)⁻¹) = (2 * Real.pi) ^ 2 := by
      field_simp [hwidth.ne']
      ring
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  field_simp
  simpa only [div_inv_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hproduct

theorem inverseCharacteristic_gaussian (width : ℝ) (hwidth : 0 < width) (x : ℝ) :
    inverseCharacteristic (fun t : ℝ => (Real.exp (-width * t ^ 2) : ℂ)) x =
      (gaussianFourierKernel width x : ℂ) := by
  have hgaussian := fourierIntegral_gaussian (b := (width : ℂ))
    (by simpa using hwidth) (-(x : ℂ))
  have hintegral : (∫ t : ℝ, Complex.exp (-(t * x : ℝ) * Complex.I) *
      (Real.exp (-width * t ^ 2) : ℂ)) =
        (Real.sqrt (Real.pi / width) : ℂ) *
          (Real.exp (-(x ^ 2 / (4 * width))) : ℂ) := by
    convert hgaussian using 1
    · congr 1
      ext t
      rw [Complex.ofReal_exp]
      congr 2 <;> push_cast <;> ring
    · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
      push_cast
      congr 2 <;> ring
  unfold inverseCharacteristic gaussianFourierKernel
  rw [hintegral]
  push_cast
  ring

end
end Universality
