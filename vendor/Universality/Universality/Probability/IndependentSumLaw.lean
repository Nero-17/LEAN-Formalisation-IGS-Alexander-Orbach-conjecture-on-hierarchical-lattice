import Universality.Probability.L2Characteristic

namespace Universality
noncomputable section
open MeasureTheory
open scoped ENNReal

def independentSumLaw {index : Type*} [Fintype index] (law : index → Measure ℝ) : Measure ℝ :=
  (Measure.pi law).map (fun value => ∑ i, value i)

instance independentSumLaw_probability {index : Type*} [Fintype index]
    (law : index → Measure ℝ) [∀ i, IsProbabilityMeasure (law i)] :
    IsProbabilityMeasure (independentSumLaw law) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem independentSumLaw_charFun {index : Type*} [Fintype index]
    (law : index → Measure ℝ) [∀ i, IsProbabilityMeasure (law i)] (t : ℝ) :
    charFun (independentSumLaw law) t = ∏ i, charFun (law i) t := by
  rw [charFun_apply_real, independentSumLaw, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : index) (x : ℝ) => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))]
  simp only [charFun_apply_real]

def finiteMixtureLaw {index : Type*} [Fintype index]
    (weight : index → ℝ) (law : index → Measure ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (weight i) • law i

theorem finiteMixtureLaw_probability {index : Type*} [Fintype index]
    (weight : index → ℝ) (law : index → Measure ℝ) [∀ i, IsProbabilityMeasure (law i)]
    (hweight : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1) :
    IsProbabilityMeasure (finiteMixtureLaw weight law) := by
  constructor
  simp only [finiteMixtureLaw, Measure.coe_finset_sum, Finset.sum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hweight i), hsum, ENNReal.ofReal_one]

theorem finiteMixtureLaw_charFun {index : Type*} [Fintype index]
    (weight : index → ℝ) (law : index → Measure ℝ) [∀ i, IsProbabilityMeasure (law i)]
    (hweight : ∀ i, 0 ≤ weight i) (t : ℝ) :
    charFun (finiteMixtureLaw weight law) t = ∑ i, (weight i : ℂ) * charFun (law i) t := by
  rw [charFun_apply_real, finiteMixtureLaw, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hweight i), charFun_apply_real]
    rfl
  · intro i _
    simpa only [Complex.ofReal_mul] using
      (integrable_characteristic_kernel (μ := law i)
        (f := fun x : ℝ => x) (by fun_prop) t).smul_measure ENNReal.ofReal_ne_top

end
end Universality
