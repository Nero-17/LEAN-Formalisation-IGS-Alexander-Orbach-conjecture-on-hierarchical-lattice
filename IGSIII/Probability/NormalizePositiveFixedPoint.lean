import IGSIII.Probability.PositiveInvariantFixedPoint
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability

open MeasureTheory Set Filter
open scoped ENNReal

theorem lp2_integral_positive {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure] (value : Lp ℝ 2 measure)
    (positive : ∀ᵐ sample ∂measure, 0 < value sample) :
    0 < ∫ sample, value sample ∂measure := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (positive.mono (fun _ inequality => inequality.le))
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp value))).mpr
  have supportEquality : Function.support value =ᵐ[measure] (Set.univ : Set Sample) := by
    filter_upwards [positive] with sample inequality
    change (value sample ≠ 0) = True
    exact propext (iff_true_intro inequality.ne')
  rw [measure_congr supportEquality, measure_univ]
  exact zero_lt_one

theorem exists_mean_one_fixed_of_positive_fixed {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (map : Lp ℝ 2 measure → Lp ℝ 2 measure)
    (homogeneous : ∀ scalar : ℝ, 0 ≤ scalar → ∀ value, map (scalar • value) = scalar • map value)
    (value : Lp ℝ 2 measure) (fixed : map value = value)
    (positive : ∀ᵐ sample ∂measure, 0 < value sample) :
    ∃ normalized : Lp ℝ 2 measure,
      map normalized = normalized ∧
      (∀ᵐ sample ∂measure, 0 < normalized sample) ∧
      (∫ sample, normalized sample ∂measure) = 1 ∧
      normalized = (∫ sample, value sample ∂measure)⁻¹ • value := by
  have meanPositive := lp2_integral_positive measure value positive
  let normalized : Lp ℝ 2 measure := (∫ sample, value sample ∂measure)⁻¹ • value
  have representative : normalized =ᵐ[measure]
      fun sample => (∫ sample, value sample ∂measure)⁻¹ * value sample := by
    filter_upwards [Lp.coeFn_smul (∫ sample, value sample ∂measure)⁻¹ value] with sample equality
    simpa only [Pi.smul_apply, smul_eq_mul] using equality
  refine ⟨normalized, ?_, ?_, ?_, rfl⟩
  · rw [homogeneous _ (inv_nonneg.mpr meanPositive.le), fixed]
  · filter_upwards [representative, positive] with sample equality inequality
    rw [equality]
    exact mul_pos (inv_pos.mpr meanPositive) inequality
  · rw [integral_congr_ae representative, integral_const_mul, inv_mul_cancel₀ meanPositive.ne']

end IGSIII.Probability
