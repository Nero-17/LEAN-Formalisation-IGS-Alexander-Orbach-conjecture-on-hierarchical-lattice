import Universality.Probability.InverseCharacteristic

namespace Universality
noncomputable section
open MeasureTheory

theorem inverseCharacteristic_norm_bound (function : ℝ → ℂ)
    (hintegrable : Integrable function) (x : ℝ) :
    ‖inverseCharacteristic function x‖ ≤ (2 * Real.pi)⁻¹ * ∫ t, ‖function t‖ := by
  have h := inverseCharacteristic_sub_bound hintegrable
    (integrable_zero ℝ ℂ volume) x
  simpa [inverseCharacteristic] using h

end
end Universality
