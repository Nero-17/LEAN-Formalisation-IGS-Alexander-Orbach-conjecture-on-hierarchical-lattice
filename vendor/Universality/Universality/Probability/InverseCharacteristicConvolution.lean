import Universality.Probability.InverseCharacteristic
import Mathlib.MeasureTheory.Integral.Prod

namespace Universality
noncomputable section
open MeasureTheory Filter

theorem inverseCharacteristic_mul_charFun (μ : Measure ℝ) [IsFiniteMeasure μ]
    (function : ℝ → ℂ) (hintegrable : Integrable function) (x : ℝ) :
    inverseCharacteristic (fun t => function t * charFun μ t) x =
      ∫ y : ℝ, inverseCharacteristic function (x - y) ∂μ := by
  have hproduct : Integrable (fun pair : ℝ × ℝ =>
      Complex.exp (-(pair.2 * (x - pair.1) : ℝ) * Complex.I) * function pair.2)
      (μ.prod volume) := by
    apply (hintegrable.norm.comp_snd μ).mono'
    · exact ((show Continuous (fun pair : ℝ × ℝ =>
        Complex.exp (-(pair.2 * (x - pair.1) : ℝ) * Complex.I)) by fun_prop).aestronglyMeasurable.mul
        (hintegrable.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume))))
    · exact Eventually.of_forall (fun pair => by simp [norm_mul, Complex.norm_exp])
  have hkernel (t : ℝ) :
      Complex.exp (-(t * x : ℝ) * Complex.I) * (function t * charFun μ t) =
        ∫ y : ℝ, Complex.exp (-(t * (x - y) : ℝ) * Complex.I) * function t ∂μ := by
    rw [charFun_apply_real, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      dsimp only
      rw [mul_comm (function t) (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)),
        ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring)
  unfold inverseCharacteristic
  simp_rw [hkernel]
  rw [← integral_integral_swap hproduct, integral_const_mul]

end
end Universality
