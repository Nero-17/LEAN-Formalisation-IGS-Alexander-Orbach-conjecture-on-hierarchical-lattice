import Universality.Probability.InverseCharacteristicRecovery
import Universality.Probability.InverseCharacteristicPositive
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

namespace Universality
noncomputable section
open MeasureTheory

theorem measure_eq_withDensity_inverseCharacteristic
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hintegrable : Integrable (charFun μ)) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (inverseCharacteristic (charFun μ) x).re) := by
  obtain ⟨hinverse, hnonnegative⟩ := inverseCharacteristic_charFun_nonnegative_integrable μ hintegrable
  have hreal : Integrable (fun x : ℝ => (inverseCharacteristic (charFun μ) x).re) := hinverse.re
  letI : IsFiniteMeasure (volume.withDensity
      (fun x => ENNReal.ofReal (inverseCharacteristic (charFun μ) x).re)) :=
    isFiniteMeasure_withDensity_ofReal hreal.hasFiniteIntegral
  apply Measure.ext_of_charFun
  funext t
  conv_rhs => rw [charFun_apply_real]
  have hmeasurable : Measurable (fun x : ℝ =>
      ENNReal.ofReal (inverseCharacteristic (charFun μ) x).re) :=
    (Complex.continuous_re.comp (continuous_inverseCharacteristic hintegrable)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul
    hmeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  calc
    charFun μ t = ∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) *
        inverseCharacteristic (charFun μ) x :=
      (integral_exp_mul_inverseCharacteristic hintegrable hinverse continuous_charFun t).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [ENNReal.toReal_ofReal (hnonnegative x).1, Complex.real_smul, (hnonnegative x).2]
        push_cast
        ring

theorem inverseCharacteristic_charFun_integral_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hintegrable : Integrable (charFun μ)) :
    (∫ x : ℝ, (inverseCharacteristic (charFun μ) x).re) = 1 := by
  have hinverse := (inverseCharacteristic_charFun_nonnegative_integrable μ hintegrable).1
  have h := integral_exp_mul_inverseCharacteristic hintegrable hinverse continuous_charFun 0
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul, charFun_zero,
    probReal_univ, Complex.ofReal_one] at h
  have hre := congrArg Complex.re h
  exact (integral_re hinverse).trans hre

end
end Universality
