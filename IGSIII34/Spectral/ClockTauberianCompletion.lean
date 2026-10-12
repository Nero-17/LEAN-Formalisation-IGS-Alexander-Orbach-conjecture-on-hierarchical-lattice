import IGSIII34.Spectral.GeometricResolventPowersCompletion
import IGSIII34.Spectral.ClockSpectralExponentCompletion
import IGSIII34.Spectral.TauberianSlack
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem eventual_power_le_positive_constant_mul_completion
    (smaller larger coefficient : ℝ) (strict : smaller < larger) (coefficientPositive : 0 < coefficient) :
    ∀ᶠ parameter : ℝ in atTop, parameter^smaller ≤ coefficient * parameter^larger := by
  have small := (tendsto_rpow_neg_atTop (sub_pos.mpr strict)).eventually (eventually_lt_nhds coefficientPositive)
  filter_upwards [eventually_gt_atTop (0 : ℝ), small] with parameter positive small
  have identity : parameter^smaller = parameter^(-(larger - smaller)) * parameter^larger := by
    rw [← Real.rpow_add positive]
    congr 1
    ring
  rw [identity]
  exact mul_le_mul_of_nonneg_right small.le (Real.rpow_pos_of_pos positive larger).le

theorem eventual_constant_mul_power_le_completion
    (smaller larger coefficient : ℝ) (strict : smaller < larger) :
    ∀ᶠ parameter : ℝ in atTop, coefficient * parameter^smaller ≤ parameter^larger := by
  have large := (tendsto_rpow_atTop (sub_pos.mpr strict)).eventually (eventually_ge_atTop coefficient)
  filter_upwards [eventually_gt_atTop (0 : ℝ), large] with parameter positive large
  have identity : parameter^larger = parameter^(larger - smaller) * parameter^smaller := by
    rw [← Real.rpow_add positive, sub_add_cancel]
  rw [identity]
  exact mul_le_mul_of_nonneg_right large (Real.rpow_pos_of_pos positive smaller).le

theorem spectral_dimension_from_true_clock_bounds_completion
    (kernel diagonal : ℝ → ℝ) (clock resistance exponent : ℝ)
    (clockAboveOne : 1 < clock) (resistancePositive : 0 < resistance)
    (exponentPositive : 0 < exponent) (exponentBelowOne : exponent < 1)
    (exponentIdentity : clock^(exponent - 1) = resistance⁻¹)
    (measurable : Measurable kernel)
    (nonnegative : ∀ time, 0 < time → 0 ≤ kernel time)
    (decreasingHeat : AntitoneOn kernel (Set.Ioi 0))
    (integrable : ∀ parameter, 0 < parameter →
      IntegrableOn (fun time => Real.exp (-parameter * time) * kernel time) (Set.Ioi 0))
    (laplaceIdentity : ∀ parameter, 1 ≤ parameter → diagonalLaplace kernel parameter = diagonal parameter)
    (decreasingResolvent : AntitoneOn diagonal (Set.Ici 1))
    (clockBounds : ∀ tolerance : ℝ, 1 < tolerance → ∀ᶠ depth : ℕ in atTop,
      1 / (resistance^depth * tolerance^depth) ≤ diagonal (clock^depth) ∧
        diagonal (clock^depth) ≤ tolerance^depth / resistance^depth) :
    Tendsto (fun time => -2 * Real.log (kernel time) / Real.log time)
      (𝓝[>] 0) (𝓝 (2 * exponent)) := by
  apply spectral_dimension_of_laplace_exponent_slack kernel exponent measurable exponentPositive exponentBelowOne
    nonnegative decreasingHeat integrable
  intro slack slackPositive
  obtain ⟨lowerCoefficient, lowerCoefficientPositive, lower⟩ := clock_slack_lower_to_power_completion diagonal clock resistance
    (exponent - 1) (exponent - 1 - slack / 2) clockAboveOne resistancePositive (by linarith)
    (by linarith) exponentIdentity decreasingResolvent (fun tolerance greater => (clockBounds tolerance greater).mono (fun _ bound => bound.1))
  obtain ⟨upperCoefficient, _, upper⟩ := clock_slack_upper_to_power_completion diagonal clock resistance
    (exponent - 1) (exponent - 1 + slack / 2) clockAboveOne resistancePositive (by linarith)
    exponentIdentity decreasingResolvent (fun tolerance greater => (clockBounds tolerance greater).mono (fun _ bound => bound.2))
  filter_upwards [lower, upper, eventually_ge_atTop (1 : ℝ),
    eventual_power_le_positive_constant_mul_completion (exponent - 1 - slack) (exponent - 1 - slack / 2)
      lowerCoefficient (by linarith) lowerCoefficientPositive,
    eventual_constant_mul_power_le_completion (exponent - 1 + slack / 2) (exponent - 1 + slack)
      upperCoefficient (by linarith)] with parameter lower upper atLeastOne absorbLower absorbUpper
  rw [laplaceIdentity parameter atLeastOne]
  exact ⟨absorbLower.trans lower, upper.trans absorbUpper⟩

end
end IGSIII34.Spectral
