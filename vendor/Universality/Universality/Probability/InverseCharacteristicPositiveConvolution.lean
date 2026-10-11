import Universality.Probability.InverseCharacteristicConvolution
import Universality.Probability.InverseCharacteristicBound
import Universality.Probability.ContinuousDensitySupport
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

namespace Universality
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem integrable_inverseCharacteristic_translate (function : ℝ → ℂ)
    (hintegrable : Integrable function) (measure : Measure ℝ) [IsFiniteMeasure measure] (x : ℝ) :
    Integrable (fun y => inverseCharacteristic function (x - y)) measure := by
  apply (integrable_const ((2 * Real.pi)⁻¹ * ∫ t, ‖function t‖)).mono'
  · exact ((continuous_inverseCharacteristic hintegrable).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y => inverseCharacteristic_norm_bound function hintegrable _)

theorem inverseCharacteristic_comp_div (function : ℝ → ℂ) (radius : ℝ)
    (hradius : 0 < radius) (x : ℝ) :
    inverseCharacteristic (fun t => function (t / radius)) x =
      (radius : ℂ) * inverseCharacteristic function (radius * x) := by
  have hkernel : (fun t : ℝ => Complex.exp (-(t * x : ℝ) * Complex.I) * function (t / radius)) =
      (fun t : ℝ => (fun s : ℝ => Complex.exp (-(s * (radius * x) : ℝ) * Complex.I) * function s)
        (t / radius)) := by
    funext t
    congr 2
    congr 2
    field_simp
  unfold inverseCharacteristic
  rw [hkernel, Measure.integral_comp_div
    (fun s : ℝ => Complex.exp (-(s * (radius * x) : ℝ) * Complex.I) * function s) radius,
    abs_of_pos hradius, Complex.real_smul]
  ring

theorem integrable_charFun_mul_charFun (first second : Measure ℝ)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hintegrable : Integrable (charFun first)) :
    Integrable (fun t => charFun first t * charFun second t) := by
  apply hintegrable.mul_bdd (c := 1) continuous_charFun.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => norm_charFun_le_one t)

theorem inverseCharacteristic_product_positive (first second : Measure ℝ)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hintegrable : Integrable (charFun first))
    (hnonnegative : ∀ x, 0 ≤ (inverseCharacteristic (charFun first) x).re)
    (hdensity : first = volume.withDensity (fun x => ENNReal.ofReal (inverseCharacteristic (charFun first) x).re))
    (hfirstSupport : ∀ x : ℝ, 0 < x → x ∈ first.support)
    (hsecondSupport : ∀ x : ℝ, 0 < x → x ∈ second.support)
    (x : ℝ) (hx : 0 < x) :
    0 < (inverseCharacteristic (fun t => charFun first t * charFun second t) x).re := by
  rw [inverseCharacteristic_mul_charFun second (charFun first) hintegrable x]
  have hre := integral_re (integrable_inverseCharacteristic_translate (charFun first) hintegrable second x)
  change (∫ y, (inverseCharacteristic (charFun first) (x - y)).re ∂second) =
    (∫ y, inverseCharacteristic (charFun first) (x - y) ∂second).re at hre
  rw [← hre]
  exact convolution_positive_of_full_positive_support first second _
    (Complex.continuous_re.comp (continuous_inverseCharacteristic hintegrable)) hnonnegative hdensity
    hfirstSupport hsecondSupport x hx
    (integrable_inverseCharacteristic_translate (charFun first) hintegrable second x).re

end
end Universality
