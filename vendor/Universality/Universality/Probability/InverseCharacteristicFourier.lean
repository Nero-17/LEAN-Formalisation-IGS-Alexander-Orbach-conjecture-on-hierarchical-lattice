import Universality.Probability.InverseCharacteristic
import Mathlib.Analysis.Fourier.FourierTransform

namespace Universality
noncomputable section
open MeasureTheory
open scoped FourierTransform

theorem inverseCharacteristic_eq_fourier (characteristic : ℝ → ℂ) (x : ℝ) :
    inverseCharacteristic characteristic x =
      (2 * Real.pi : ℂ)⁻¹ * (𝓕 characteristic) (x / (2 * Real.pi)) := by
  unfold inverseCharacteristic
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [smul_eq_mul]
    congr 2
    have hscale : -2 * Real.pi * t * (x / (2 * Real.pi)) = -(t * x) := by
      field_simp [Real.pi_ne_zero]
    rw [hscale]
    push_cast
    ring)

end
end Universality
