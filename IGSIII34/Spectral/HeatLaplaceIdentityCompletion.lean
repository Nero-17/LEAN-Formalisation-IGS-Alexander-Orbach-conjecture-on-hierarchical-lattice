import IGSIII34.Spectral.IndexedHeatSeriesCompletion
import IGSIII34.Spectral.LaplaceMonotone
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The Laplace transform of a nonnegative diagonal spectral series is
proved by Bochner dominated convergence, not assumed as a resolvent input. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem exponential_weight_integral_completion
    (parameter eigenvalue coefficient : ℝ) (parameterPositive : 0 < parameter)
    (eigenvalueNonnegative : 0 ≤ eigenvalue) :
    (∫ time : ℝ in Ioi 0, Real.exp (-(parameter + eigenvalue) * time) * coefficient) =
      coefficient / (parameter + eigenvalue) := by
  have negative : -(parameter + eigenvalue) < 0 := by linarith
  rw [integral_mul_const, integral_exp_mul_Ioi negative]
  simp only [mul_zero, Real.exp_zero]
  simp only [div_neg, neg_div, neg_neg]
  ring

theorem diagonal_spectral_series_laplace_completion
    {Index : Type*} [Countable Index] (eigenvalues coefficients : Index → ℝ)
    (nonnegativeEigenvalues : ∀ index, 0 ≤ eigenvalues index)
    (nonnegativeCoefficients : ∀ index, 0 ≤ coefficients index)
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (summable : Summable (fun index => coefficients index / (parameter + eigenvalues index))) :
    diagonalLaplace (fun time => ∑' index, Real.exp (-time * eigenvalues index) * coefficients index) parameter =
      ∑' index, coefficients index / (parameter + eigenvalues index) := by
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
    exact exponential_weight_integral_completion _ _ _ parameterPositive (nonnegativeEigenvalues index)
  have exchange := integral_tsum_of_summable_integral_norm integrableTerms
    (by simpa only [integralNorm] using summable)
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
  unfold diagonalLaplace
  rw [damped, ← exchange]
  apply tsum_congr
  intro index
  exact exponential_weight_integral_completion _ _ _ parameterPositive (nonnegativeEigenvalues index)

theorem indexed_spectral_heat_diagonal_laplace_completion
    {Space Index : Type*} [Countable Index]
    (eigenvalues : Index → ℝ) (eigenfunctions : Index → Space → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index)
    (parameter : ℝ) (parameterPositive : 0 < parameter) (point : Space)
    (summable : Summable (fun index => eigenfunctions index point ^ 2 / (parameter + eigenvalues index))) :
    diagonalLaplace (fun time => indexedSpectralHeatKernelCompletion eigenvalues eigenfunctions time point point) parameter =
      ∑' index, eigenfunctions index point ^ 2 / (parameter + eigenvalues index) := by
  have identity := diagonal_spectral_series_laplace_completion eigenvalues
    (fun index => eigenfunctions index point ^ 2) nonnegative (fun index => sq_nonneg _) parameter parameterPositive summable
  simpa only [indexedSpectralHeatKernelCompletion, pow_two, mul_assoc] using identity

end
end IGSIII34.Spectral
