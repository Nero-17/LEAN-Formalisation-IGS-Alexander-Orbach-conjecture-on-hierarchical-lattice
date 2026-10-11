import Universality.Probability.InverseCharacteristicFourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace Universality
noncomputable section
open MeasureTheory
open scoped FourierTransform

theorem contDiff_inverseCharacteristic {characteristic : ℝ → ℂ} {order : ℕ∞}
    (h : ∀ n : ℕ, n ≤ order → Integrable (fun t : ℝ => ‖t‖ ^ n * ‖characteristic t‖)) :
    ContDiff ℝ order (inverseCharacteristic characteristic) := by
  have heq : inverseCharacteristic characteristic = fun x =>
      (2 * Real.pi : ℂ)⁻¹ * (𝓕 characteristic) (x / (2 * Real.pi)) :=
    funext (inverseCharacteristic_eq_fourier characteristic)
  rw [heq]
  exact contDiff_const.mul ((Real.contDiff_fourier h).comp (contDiff_id.div_const _))

end
end Universality
