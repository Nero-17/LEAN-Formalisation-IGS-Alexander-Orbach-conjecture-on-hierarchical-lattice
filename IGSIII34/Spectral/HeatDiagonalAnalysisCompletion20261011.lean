import IGSIII34.Spectral.HeatLaplaceIdentityCompletion20261011
import IGSIII34.Spectral.IntegrableSeriesCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

variable {Index : Type*}

theorem diagonal_resolvent_summable_all_positive_completion20261011
    (eigenvalues coefficients : Index → ℝ)
    (nonnegativeEigenvalues : ∀ index, 0 ≤ eigenvalues index)
    (nonnegativeCoefficients : ∀ index, 0 ≤ coefficients index)
    (baseSummable : Summable (fun index => coefficients index / (1 + eigenvalues index)))
    (parameter : ℝ) (positive : 0 < parameter) :
    Summable (fun index => coefficients index / (parameter + eigenvalues index)) := by
  by_cases atLeastOne : 1 ≤ parameter
  · apply Summable.of_nonneg_of_le
      (fun index => div_nonneg (nonnegativeCoefficients index) (by linarith [nonnegativeEigenvalues index]))
      (fun index => div_le_div_of_nonneg_left (nonnegativeCoefficients index)
        (by linarith [nonnegativeEigenvalues index]) (by linarith)) baseSummable
  · apply Summable.of_nonneg_of_le
      (fun index => div_nonneg (nonnegativeCoefficients index) (by linarith [nonnegativeEigenvalues index]))
      (f := fun index => parameter⁻¹ * (coefficients index / (1 + eigenvalues index)))
      _ (baseSummable.mul_left _)
    intro index
    have bound : parameter * (1 + eigenvalues index) ≤ parameter + eigenvalues index := by
      nlinarith [nonnegativeEigenvalues index]
    have comparison := div_le_div_of_nonneg_left (nonnegativeCoefficients index)
      (mul_pos positive (by linarith [nonnegativeEigenvalues index])) bound
    simpa only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm] using comparison

theorem diagonal_spectral_series_integrable_completion20261011 [Countable Index]
    (eigenvalues coefficients : Index → ℝ)
    (nonnegativeEigenvalues : ∀ index, 0 ≤ eigenvalues index)
    (nonnegativeCoefficients : ∀ index, 0 ≤ coefficients index)
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (summable : Summable (fun index => coefficients index / (parameter + eigenvalues index))) :
    IntegrableOn (fun time => Real.exp (-parameter * time) *
      (∑' index, Real.exp (-time * eigenvalues index) * coefficients index)) (Ioi 0) := by
  have integrableTerms : ∀ index, IntegrableOn
      (fun time : ℝ => Real.exp (-(parameter + eigenvalues index) * time) * coefficients index) (Ioi 0) := by
    intro index
    exact (integrableOn_exp_mul_Ioi (by linarith [nonnegativeEigenvalues index]) 0).mul_const _
  have integralNorm : ∀ index,
      (∫ time : ℝ in Ioi 0, ‖Real.exp (-(parameter + eigenvalues index) * time) * coefficients index‖) =
        coefficients index / (parameter + eigenvalues index) := by
    intro index
    simp only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (nonnegativeCoefficients index))]
    exact exponential_weight_integral_completion20261011 _ _ _ parameterPositive (nonnegativeEigenvalues index)
  have integrated := integrable_tsum_of_summable_integral_norm_completion20261011
    (volume.restrict (Ioi 0)) _ integrableTerms (by simpa only [integralNorm] using summable)
  have damped : (fun time : ℝ => Real.exp (-parameter * time) *
      (∑' index, Real.exp (-time * eigenvalues index) * coefficients index)) =
      (fun time : ℝ => ∑' index, Real.exp (-(parameter + eigenvalues index) * time) * coefficients index) := by
    funext time
    rw [← tsum_mul_left]
    apply tsum_congr
    intro index
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [damped]
  exact integrated

theorem diagonal_heat_series_summable_completion20261011
    (eigenvalues coefficients : Index → ℝ)
    (nonnegativeEigenvalues : ∀ index, 0 ≤ eigenvalues index)
    (nonnegativeCoefficients : ∀ index, 0 ≤ coefficients index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (baseSummable : Summable (fun index => coefficients index / (1 + eigenvalues index)))
    (time : ℝ) (positive : 0 < time) :
    Summable (fun index => Real.exp (-time * eigenvalues index) * coefficients index) := by
  apply baseSummable.of_norm_bounded_eventually
  have small := (indexed_exponential_spectral_weight_tendsto_zero_completion20261011 eigenvalues diverge time positive).eventually
    (gt_mem_nhds zero_lt_one)
  filter_upwards [small] with index bound
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (nonnegativeCoefficients index))]
  have denominatorPositive : 0 < 1 + eigenvalues index := by linarith [nonnegativeEigenvalues index]
  calc
    _ = ((1 + eigenvalues index) * Real.exp (-time * eigenvalues index)) *
        (coefficients index / (1 + eigenvalues index)) := by field_simp
    _ ≤ 1 * (coefficients index / (1 + eigenvalues index)) :=
      mul_le_mul_of_nonneg_right bound.le (div_nonneg (nonnegativeCoefficients index) denominatorPositive.le)
    _ = _ := one_mul _

theorem diagonal_heat_series_antitone_completion20261011
    (eigenvalues coefficients : Index → ℝ)
    (nonnegativeEigenvalues : ∀ index, 0 ≤ eigenvalues index)
    (nonnegativeCoefficients : ∀ index, 0 ≤ coefficients index)
    (diverge : Tendsto eigenvalues cofinite atTop)
    (baseSummable : Summable (fun index => coefficients index / (1 + eigenvalues index))) :
    AntitoneOn (fun time => ∑' index, Real.exp (-time * eigenvalues index) * coefficients index) (Ioi 0) := by
  intro first firstPositive second secondPositive ordered
  apply (diagonal_heat_series_summable_completion20261011 eigenvalues coefficients nonnegativeEigenvalues
    nonnegativeCoefficients diverge baseSummable second secondPositive).tsum_le_tsum _
    (diagonal_heat_series_summable_completion20261011 eigenvalues coefficients nonnegativeEigenvalues
      nonnegativeCoefficients diverge baseSummable first firstPositive)
  intro index
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [nonnegativeEigenvalues index]))
    (nonnegativeCoefficients index)

end
end IGSIII34.Spectral
