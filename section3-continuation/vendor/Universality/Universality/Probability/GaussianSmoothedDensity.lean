import Universality.Probability.GaussianFourierKernel
import Universality.Probability.InverseCharacteristicConvolution

namespace Universality
noncomputable section
open MeasureTheory Filter

def gaussianSmoothedDensity (μ : Measure ℝ) (width x : ℝ) : ℝ :=
  ∫ y : ℝ, gaussianFourierKernel width (x - y) ∂μ

theorem gaussianSmoothedDensity_nonneg (μ : Measure ℝ) (width x : ℝ) :
    0 ≤ gaussianSmoothedDensity μ width x :=
  integral_nonneg (fun y => gaussianFourierKernel_nonneg width (x - y))

theorem integrable_gaussian_kernel_product (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (width : ℝ) (hwidth : 0 < width) :
    Integrable (fun pair : ℝ × ℝ => gaussianFourierKernel width (pair.2 - pair.1))
      (μ.prod volume) := by
  apply (integrable_prod_iff (by unfold gaussianFourierKernel; fun_prop)).mpr
  constructor
  · exact Eventually.of_forall (fun y => (integrable_gaussianFourierKernel width hwidth).comp_sub_right y)
  · have hnorm (y x : ℝ) : ‖gaussianFourierKernel width (x - y)‖ =
        gaussianFourierKernel width (x - y) :=
      Real.norm_of_nonneg (gaussianFourierKernel_nonneg width (x - y))
    simp_rw [hnorm, integral_sub_right_eq_self, integral_gaussianFourierKernel width hwidth]
    exact integrable_const 1

theorem integrable_gaussianSmoothedDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (width : ℝ) (hwidth : 0 < width) : Integrable (gaussianSmoothedDensity μ width) :=
  (integrable_gaussian_kernel_product μ width hwidth).integral_prod_right

theorem integral_gaussianSmoothedDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (width : ℝ) (hwidth : 0 < width) :
    (∫ x : ℝ, gaussianSmoothedDensity μ width x) = 1 := by
  unfold gaussianSmoothedDensity
  rw [← integral_integral_swap (integrable_gaussian_kernel_product μ width hwidth)]
  simp_rw [integral_sub_right_eq_self, integral_gaussianFourierKernel width hwidth]
  simp

theorem inverseCharacteristic_gaussian_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (width : ℝ) (hwidth : 0 < width) (x : ℝ) :
    inverseCharacteristic (fun t : ℝ => (Real.exp (-width * t ^ 2) : ℂ) * charFun μ t) x =
      (gaussianSmoothedDensity μ width x : ℂ) := by
  rw [inverseCharacteristic_mul_charFun μ _ (by
    exact (integrable_exp_neg_mul_sq hwidth).ofReal)]
  simp_rw [inverseCharacteristic_gaussian width hwidth]
  exact integral_ofReal (𝕜 := ℂ)

end
end Universality
