import Universality.Probability.CharacteristicRigidity
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Equality at an extreme point of the complex unit disk holds almost surely. -/
theorem ae_eq_one_of_integral_eq_one [IsProbabilityMeasure μ]
    (f : Ω → ℂ) (hf : Integrable f μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1) (hmean : ∫ x, f x ∂μ = 1) :
    ∀ᵐ x ∂μ, f x = 1 := by
  have hnonnegative : ∀ᵐ x ∂μ, 0 ≤ 1 - (f x).re := by
    filter_upwards [hbound] with x hx
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hx)
  have hzero : ∫ x, 1 - (f x).re ∂μ = 0 := by
    change (∫ x, 1 - RCLike.re (f x) ∂μ) = 0
    rw [integral_sub (integrable_const (1 : ℝ)) hf.re, integral_re hf, hmean]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonnegative
    ((integrable_const (1 : ℝ)).sub hf.re)).mp hzero
  filter_upwards [hae, hbound] with x hx hnorm
  have hre : (f x).re = 1 := (sub_eq_zero.mp hx).symm
  apply Complex.ext
  · simpa using hre
  · have hle : ‖f x‖ ≤ (f x).re := by rw [hre]; exact hnorm
    simpa using RCLike.im_eq_zero_of_le hle

/-- Unit characteristic modulus forces a fixed phase almost surely. -/
theorem characteristic_unit_phase [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (t : ℝ)
    (hunit : ‖randomCharacteristic μ f t‖ = 1) :
    ∀ᵐ x ∂μ, Complex.exp ((t * f x : ℝ) * Complex.I) = randomCharacteristic μ f t := by
  have hne : randomCharacteristic μ f t ≠ 0 := by intro hz; simpa [hz] using hunit
  have heq := ae_eq_one_of_integral_eq_one
    (μ := μ) (fun x => Complex.exp ((t * f x : ℝ) * Complex.I) / randomCharacteristic μ f t)
    ((integrable_characteristic_kernel hf t).div_const _)
    (Eventually.of_forall (fun x => by
      rw [norm_div, Complex.norm_exp_ofReal_mul_I, hunit, div_one]))
    (by rw [integral_div]; exact div_self hne)
  exact heq.mono (fun x hx => (div_eq_one_iff_eq hne).mp hx)

/-- A sequence of nonzero frequencies tending to zero separates real values. -/
theorem real_eq_of_small_characteristic_phases (frequency : ℕ → ℝ)
    (hfrequency : Tendsto frequency atTop (𝓝 0)) (hne : ∀ n, frequency n ≠ 0)
    (x y : ℝ)
    (hphase : ∀ n, Complex.exp ((frequency n * x : ℝ) * Complex.I) =
      Complex.exp ((frequency n * y : ℝ) * Complex.I)) : x = y := by
  have hx : Tendsto (fun n => frequency n * x) atTop (𝓝 0) := by
    simpa using hfrequency.mul_const x
  have hy : Tendsto (fun n => frequency n * y) atTop (𝓝 0) := by
    simpa using hfrequency.mul_const y
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := ((hx.eventually (Ioo_mem_nhds (by linarith : -Real.pi < (0 : ℝ)) hpi)).and
    (hy.eventually (Ioo_mem_nhds (by linarith : -Real.pi < (0 : ℝ)) hpi))).exists
  have hphaseEq := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (frequency n * x : ℝ) * Complex.I) (y := (frequency n * y : ℝ) * Complex.I)
    (by simpa using hn.1.1) (by simpa using hn.1.2.le)
    (by simpa using hn.2.1) (by simpa using hn.2.2.le) (hphase n)
  have hproduct : frequency n * x = frequency n * y := by
    simpa using congrArg Complex.im hphaseEq
  exact mul_left_cancel₀ (hne n) hproduct

/-- A nonconstant real law cannot have unit characteristic modulus along
nonzero frequencies converging to zero. No moment or Taylor assumption is used. -/
theorem ae_constant_of_characteristic_unit_sequence [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (frequency : ℕ → ℝ) (hfrequency : Tendsto frequency atTop (𝓝 0))
    (hne : ∀ n, frequency n ≠ 0)
    (hunit : ∀ n, ‖randomCharacteristic μ f (frequency n)‖ = 1) :
    ∃ constant : ℝ, ∀ᵐ x ∂μ, f x = constant := by
  have hall : ∀ᵐ x ∂μ, ∀ n,
      Complex.exp ((frequency n * f x : ℝ) * Complex.I) = randomCharacteristic μ f (frequency n) :=
    ae_all_iff.mpr (fun n => characteristic_unit_phase f hf (frequency n) (hunit n))
  obtain ⟨point, hpoint⟩ := hall.exists
  refine ⟨f point, hall.mono (fun x hx => ?_)⟩
  exact real_eq_of_small_characteristic_phases frequency hfrequency hne (f x) (f point)
    (fun n => (hx n).trans (hpoint n).symm)

end
end Universality
