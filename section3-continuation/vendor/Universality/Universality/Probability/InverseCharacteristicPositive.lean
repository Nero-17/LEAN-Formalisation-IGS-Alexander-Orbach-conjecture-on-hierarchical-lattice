import Universality.Probability.GaussianDamping
import Universality.Probability.GaussianSmoothedDensity

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

theorem inverseCharacteristic_charFun_nonnegative_integrable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hcharacteristic : Integrable (charFun μ)) :
    Integrable (inverseCharacteristic (charFun μ)) ∧
      ∀ x : ℝ, 0 ≤ (inverseCharacteristic (charFun μ) x).re ∧
        (((inverseCharacteristic (charFun μ) x).re : ℝ) : ℂ) =
          inverseCharacteristic (charFun μ) x := by
  have hwidth (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hform (n : ℕ) (x : ℝ) :=
    inverseCharacteristic_gaussian_charFun μ (1 / ((n : ℝ) + 1)) (hwidth n) x
  have hconvergence (x : ℝ) :
      Tendsto (fun n : ℕ => (gaussianSmoothedDensity μ (1 / ((n : ℝ) + 1)) x : ℂ))
        atTop (𝓝 (inverseCharacteristic (charFun μ) x)) := by
    have hlimit := inverseCharacteristic_gaussianDamping_tendsto (charFun μ) hcharacteristic x
    simpa only [hform] using hlimit
  have hreal (x : ℝ) :
      Tendsto (fun n : ℕ => gaussianSmoothedDensity μ (1 / ((n : ℝ) + 1)) x)
        atTop (𝓝 (inverseCharacteristic (charFun μ) x).re) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp (hconvergence x)
  have hnonnegative (x : ℝ) : 0 ≤ (inverseCharacteristic (charFun μ) x).re := by
    exact ge_of_tendsto (hreal x) (Eventually.of_forall
      (fun n => gaussianSmoothedDensity_nonneg μ (1 / ((n : ℝ) + 1)) x))
  have hrealValue (x : ℝ) : (((inverseCharacteristic (charFun μ) x).re : ℝ) : ℂ) =
      inverseCharacteristic (charFun μ) x := by
    have himag : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (inverseCharacteristic (charFun μ) x).im) := by
      simpa only [Function.comp_def, Complex.ofReal_im] using
        Complex.continuous_im.continuousAt.tendsto.comp (hconvergence x)
    have hzero := tendsto_nhds_unique tendsto_const_nhds himag
    apply Complex.ext
    · simp
    · simpa using hzero
  have hnormIntegral (n : ℕ) :
      (∫⁻ x : ℝ, ‖gaussianSmoothedDensity μ (1 / ((n : ℝ) + 1)) x‖ₑ) = 1 := by
    simp_rw [Real.enorm_of_nonneg (gaussianSmoothedDensity_nonneg μ _ _)]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_gaussianSmoothedDensity μ _ (hwidth n))
      (Eventually.of_forall (gaussianSmoothedDensity_nonneg μ _))]
    rw [integral_gaussianSmoothedDensity μ _ (hwidth n)]
    simp
  have hrealIntegrable : Integrable (fun x : ℝ => (inverseCharacteristic (charFun μ) x).re) := by
    apply integrable_of_tendsto (Eventually.of_forall hreal)
      (fun n => (integrable_gaussianSmoothedDensity μ _ (hwidth n)).aestronglyMeasurable)
    simp only [hnormIntegral, liminf_const]
    exact ENNReal.one_ne_top
  refine ⟨?_, fun x => ⟨hnonnegative x, hrealValue x⟩⟩
  exact hrealIntegrable.ofReal.congr (Eventually.of_forall hrealValue)

end
end Universality
