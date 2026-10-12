import IGSIII4.SpectralDensity.ActualSharpMassUpper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork Filter Topology

theorem appendix_actual_mass_strict_lower (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : (appendixRule base length).network.reliability probability = probability)
    (aboveHalf : 1 / 2 ≤ probability) :
    (blockCount base length : ℝ) * (pathCount length : ℝ) / 3 <
      actualMassGrowth (appendixRule base length) probability := by
  have connectedLower := actual_connected_mass_lower (blockCount base length) (pathCount length)
    (length - 2) probability positive belowOne fixedPoint
  have radiusLower := (appendixRule_classical base length lengthLarge).mass_spectralRadius_strictly_gt_connected_entry positive belowOne
  have coefficientLower : (1 / 3 : ℝ) ≤ probability / (1 + probability) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + probability)).mpr
    linarith
  have scaledLower := mul_le_mul_of_nonneg_left coefficientLower
    (by positivity : 0 ≤ ((blockCount base length * pathCount length : ℕ) : ℝ))
  have strictBound := scaledLower.trans_lt (connectedLower.trans_lt radiusLower)
  simpa only [Nat.cast_mul, actualMassGrowth, div_eq_mul_inv, one_mul] using strictBound

/-- Both numerical mass estimates in Appendix C hold for the actual family
at its own finite-rule critical points. -/
theorem appendix_actual_mass_sharp_bounds (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      (blockCount base length : ℝ) * (pathCount length : ℝ) / 3 <
          actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length) ∧
        actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length) <
          50 * (blockCount base length : ℝ) * (pathCount length : ℝ) + 4 := by
  filter_upwards [appendix_actual_mass_sharp_upper base baseAboveOne,
    appendixCriticalProbability_interval_eventually base baseAboveOne, eventually_ge_atTop (2 : ℕ)] with length upper interval lengthLarge
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthLarge
  exact ⟨appendix_actual_mass_strict_lower base length lengthLarge _ positive belowOne fixedPoint (by linarith [interval.1]), upper⟩

end
end IGSIII4.SpectralDensity.ActualFamily


