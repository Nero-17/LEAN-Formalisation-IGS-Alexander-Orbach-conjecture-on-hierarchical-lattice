import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability

open MeasureTheory Filter
open scoped ENNReal Topology

theorem eLpNorm_tendsto_zero_of_dominated_ae
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (order : ℝ≥0∞) (orderPositive : order ≠ 0) (orderFinite : order ≠ ∞)
    (sequence : ℕ → Sample → ℝ) (limit dominator : Sample → ℝ)
    (measurable : ∀ depth, AEStronglyMeasurable (sequence depth) measure)
    (limitMeasurable : AEStronglyMeasurable limit measure)
    (dominatorMemLp : MemLp dominator order measure)
    (bounds : ∀ depth, ∀ᵐ sample ∂measure, ‖sequence depth sample - limit sample‖ ≤ ‖dominator sample‖)
    (convergence : ∀ᵐ sample ∂measure, Tendsto (fun depth => sequence depth sample) atTop (𝓝 (limit sample))) :
    Tendsto (fun depth => eLpNorm (sequence depth - limit) order measure) atTop (𝓝 0) := by
  have orderRealPositive := ENNReal.toReal_pos orderPositive orderFinite
  have powersTendsto : Tendsto (fun depth =>
      ∫⁻ sample, ‖sequence depth sample - limit sample‖ₑ ^ order.toReal ∂measure) atTop (𝓝 0) := by
    have result := tendsto_lintegral_of_dominated_convergence'
      (fun sample => ‖dominator sample‖ₑ ^ order.toReal)
      (fun depth => ((measurable depth).sub limitMeasurable).enorm.pow_const order.toReal)
      (fun depth => (bounds depth).mono (fun sample inequality =>
        ENNReal.rpow_le_rpow (by simpa only [← ofReal_norm, Pi.sub_apply] using ENNReal.ofReal_le_ofReal inequality) orderRealPositive.le))
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top orderPositive orderFinite dominatorMemLp.eLpNorm_lt_top).ne
      (show ∀ᵐ sample ∂measure, Tendsto
          (fun depth => ‖sequence depth sample - limit sample‖ₑ ^ order.toReal) atTop (𝓝 (0 : ℝ≥0∞)) from by
        filter_upwards [convergence] with sample sampleConvergence
        have normTendsto : Tendsto (fun depth => ‖sequence depth sample - limit sample‖ₑ) atTop (𝓝 0) := by
          simpa only [sub_self, enorm_zero] using (sampleConvergence.sub_const (limit sample)).enorm
        simpa only [ENNReal.zero_rpow_of_pos orderRealPositive, Function.comp_def] using
          ((ENNReal.continuous_rpow_const (y := order.toReal)).tendsto (0 : ℝ≥0∞)).comp normTendsto)
    simpa only [lintegral_zero, Pi.sub_apply] using result
  have rooted := ((ENNReal.continuous_rpow_const (y := 1 / order.toReal)).tendsto (0 : ℝ≥0∞)).comp powersTendsto
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal orderPositive orderFinite, Pi.sub_apply,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr orderRealPositive), Function.comp_def] using rooted

end IGSIII.Probability
