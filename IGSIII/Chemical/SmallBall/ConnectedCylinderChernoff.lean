import IGSIII.Chemical.SmallBall.MeasurePairedBarrier
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

theorem bernoulli_lower_tail_exponent_positive : 0 < (1 / 2 : ℝ) - Real.exp (-1) := by
  rw [Real.exp_neg]
  have inequality : (Real.exp 1)⁻¹ < (1 / 2 : ℝ) := by
    simpa only [inv_eq_one_div] using (inv_lt_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two
  linarith

theorem bernoulli_centered_exponential_integral_le
    {Sample : Type*} [MeasurableSpace Sample] (μ : Measure Sample) [IsProbabilityMeasure μ]
    (good : Set Sample) (goodMeasurable : MeasurableSet good) :
    Integrable (fun sample => Real.exp (μ.real good / 2 - good.indicator (fun _ => (1 : ℝ)) sample)) μ ∧
    (∫ sample, Real.exp (μ.real good / 2 - good.indicator (fun _ => (1 : ℝ)) sample) ∂μ) ≤
      Real.exp (-μ.real good * ((1 / 2 : ℝ) - Real.exp (-1))) := by
  have indicatorNonnegative (sample : Sample) : 0 ≤ good.indicator (fun _ => (1 : ℝ)) sample :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) sample
  have integrable : Integrable (fun sample => Real.exp (μ.real good / 2 - good.indicator (fun _ => (1 : ℝ)) sample)) μ := by
    apply (integrable_const (Real.exp (μ.real good / 2))).mono'
      (measurable_const.sub (measurable_const.indicator goodMeasurable)).exp.aestronglyMeasurable
    filter_upwards [] with sample
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact sub_le_self _ (indicatorNonnegative sample)
  refine ⟨integrable, ?_⟩
  have equality : (fun sample => Real.exp (μ.real good / 2 - good.indicator (fun _ => (1 : ℝ)) sample)) =
      fun sample => Real.exp (μ.real good / 2) * (1 + good.indicator (fun _ => Real.exp (-1) - 1) sample) := by
    funext sample
    by_cases membership : sample ∈ good
    · simp only [Set.indicator_of_mem membership]
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    · simp only [Set.indicator_of_notMem membership, sub_zero, add_zero, mul_one]
  rw [equality, integral_const_mul, integral_add (integrable_const 1)
    ((integrable_const (Real.exp (-1) - 1)).indicator goodMeasurable), integral_const,
    integral_indicator_const _ goodMeasurable]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  have tangent := Real.add_one_le_exp (-μ.real good * (1 - Real.exp (-1)))
  calc
    Real.exp (μ.real good / 2) * (1 + (μ good).toReal * (Real.exp (-1) - 1)) ≤
        Real.exp (μ.real good / 2) * Real.exp (-μ.real good * (1 - Real.exp (-1))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      have coefficientEquality : 1 + (μ good).toReal * (Real.exp (-1) - 1) =
          -μ.real good * (1 - Real.exp (-1)) + 1 := by rw [measureReal_def]; ring
      rw [coefficientEquality]
      exact tangent
    _ = _ := by rw [← Real.exp_add]; congr 1; simp only [measureReal_def]; ring

theorem independent_good_count_lower_tail
    {Index Sample : Type*} [Fintype Index] [DecidableEq Index] [MeasurableSpace Sample]
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (good : Set Sample) (goodMeasurable : MeasurableSet good) (selected : Finset Index) :
    (Measure.pi (fun _ : Index => μ)).real
      {samples | (∑ index ∈ selected, good.indicator (fun _ => (1 : ℝ)) (samples index)) <
        μ.real good / 2 * selected.card} ≤
      Real.exp (-μ.real good * ((1 / 2 : ℝ) - Real.exp (-1)) * selected.card) := by
  have factorMoment := bernoulli_centered_exponential_integral_le μ good goodMeasurable
  have bound := measure_product_paired_path_barrier (fun _ : Index => μ)
    (fun _ _ => μ.real good / 2) (fun _ => good.indicator (fun _ => (1 : ℝ)))
    (fun _ => measurable_const) (fun _ => measurable_const.indicator goodMeasurable)
    selected (parameter := 1) (scale := 1) (by norm_num)
    (fun _ _ => by simpa only [one_mul] using factorMoment.1)
    (fun _ _ => by simpa only [one_mul] using factorMoment.2)
  have equality : (Real.exp (-μ.real good * ((1 / 2 : ℝ) - Real.exp (-1)))) ^ selected.card =
      Real.exp (-μ.real good * ((1 / 2 : ℝ) - Real.exp (-1)) * selected.card) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [equality] at bound
  simpa only [PathFamily.pathCost, one_mul, Finset.sum_const, nsmul_eq_mul, mul_comm (selected.card : ℝ)] using bound

end
end IGSIII.Chemical.SmallBall