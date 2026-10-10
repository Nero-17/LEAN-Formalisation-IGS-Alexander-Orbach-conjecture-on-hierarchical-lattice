import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

theorem lp2_positive_weighted_difference_mean_le
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (first second weight : Lp ℝ 2 measure) :
    (∫ sample, max (first sample-second sample) 0 * weight sample ∂measure) ≤
      ‖first-second‖ * ‖weight‖ := by
  have innerEquality : (∫ sample, max (first sample-second sample) 0 * weight sample ∂measure) =
      inner ℝ weight ((first-second) ⊔ 0) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sup (first-second) 0, Lp.coeFn_sub first second, Lp.coeFn_zero ℝ 2 measure]
      with sample supremum subtraction zero
    change max (first sample-second sample) 0 * weight sample = ((first-second) ⊔ 0) sample * weight sample
    rw [supremum]
    change _ = max ((first-second) sample) ((0 : Lp ℝ 2 measure) sample) * weight sample
    rw [subtraction, Pi.sub_apply, zero]
    rfl
  rw [innerEquality]
  have positivePartNorm : ‖(first-second) ⊔ 0‖ ≤ ‖first-second‖ := by
    simpa only [sup_idem, sub_zero] using norm_sup_sub_sup_le_norm (first-second) 0 0
  exact (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left positivePartNorm (norm_nonneg weight)).trans_eq (mul_comm _ _))

theorem lp2_weighted_positive_difference_tendsto_zero
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (sequence : ℕ → Lp ℝ 2 measure) (limit : Lp ℝ 2 measure)
    (convergence : Tendsto sequence atTop (𝓝 limit))
    (weights : ℕ → Lp ℝ 2 measure) (weightsNonnegative : ∀ depth, 0 ≤ weights depth)
    (bound : ℝ) (bounded : ∀ depth, ‖weights depth‖ ≤ bound) :
    Tendsto (fun depth => ∫ sample, max (sequence depth sample-limit sample) 0 * weights depth sample ∂measure)
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro depth
    exact integral_nonneg_of_ae (by
      filter_upwards [(Lp.coeFn_nonneg (weights depth)).mpr (weightsNonnegative depth)] with sample nonnegative
      exact mul_nonneg (le_max_right _ _) nonnegative)
  · intro depth
    exact (lp2_positive_weighted_difference_mean_le measure (sequence depth) limit (weights depth)).trans
      (mul_le_mul_of_nonneg_left (bounded depth) (norm_nonneg _))
  · have normConvergence := (convergence.sub_const limit).norm
    simpa only [sub_self, norm_zero, zero_mul] using normConvergence.mul_const bound

end
end IGSIII34.Probability


