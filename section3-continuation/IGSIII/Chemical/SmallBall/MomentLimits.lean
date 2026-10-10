import IGSIII.Probability.OmegaOrbit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Filter IGSIII.Probability
open scoped ENNReal Topology

noncomputable section

variable {Sample : Type*} [MeasurableSpace Sample]

theorem lintegral_le_of_ae_tendsto_of_uniform_bound (measure : Measure Sample)
    (response : ℕ → Sample → ℝ≥0∞) (limit : Sample → ℝ≥0∞)
    (measurable : ∀ depth, AEMeasurable (response depth) measure)
    (convergence : ∀ᵐ sample ∂measure, Tendsto (fun depth => response depth sample) atTop (𝓝 (limit sample)))
    (bound : ℝ≥0∞) (bounds : ∀ depth, (∫⁻ sample, response depth sample ∂measure) ≤ bound) :
    (∫⁻ sample, limit sample ∂measure) ≤ bound := by
  calc
    _ = ∫⁻ sample, liminf (fun depth => response depth sample) atTop ∂measure :=
      lintegral_congr_ae (convergence.mono (fun _ pointwise => pointwise.liminf_eq.symm))
    _ ≤ liminf (fun depth => ∫⁻ sample, response depth sample ∂measure) atTop :=
      lintegral_liminf_le' measurable
    _ ≤ bound := liminf_le_of_frequently_le' (Filter.Frequently.of_forall bounds)

theorem orbitClusterSet_lintegral_continuous_response_le (measure : Measure Sample)
    {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]
    (sequence : ℕ → Lp ℝ exponent measure) (point : Lp ℝ exponent measure)
    (cluster : point ∈ orbitClusterSet sequence)
    (response : ℝ → ℝ≥0∞) (continuous : Continuous response)
    (bound : ℝ≥0∞) (bounds : ∀ depth, (∫⁻ sample, response (sequence depth sample) ∂measure) ≤ bound) :
    (∫⁻ sample, response (point sample) ∂measure) ≤ bound := by
  obtain ⟨subsequence, increasing, convergence⟩ := cluster.tendsto_subseq
  obtain ⟨subsubsequence, subIncreasing, pointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp convergence).exists_seq_tendsto_ae
  apply lintegral_le_of_ae_tendsto_of_uniform_bound measure
    (fun depth sample => response (sequence (subsequence (subsubsequence depth)) sample))
    (fun sample => response (point sample)) _ _ bound
    (fun depth => bounds (subsequence (subsubsequence depth)))
  · intro depth
    exact continuous.measurable.comp_aemeasurable (Lp.aestronglyMeasurable _).aemeasurable
  · filter_upwards [pointwise] with sample limit
    exact (continuous.tendsto (point sample)).comp limit

theorem ae_positive_of_lintegral_inverse_ofReal_lt_top (measure : Measure Sample)
    (value : Sample → ℝ) (measurable : AEMeasurable value measure)
    (finiteInverse : (∫⁻ sample, (ENNReal.ofReal (value sample))⁻¹ ∂measure) ≠ ∞) :
    ∀ᵐ sample ∂measure, 0 < value sample := by
  have finite := ae_lt_top'
    ((ENNReal.continuous_ofReal.measurable.comp_aemeasurable measurable).inv) finiteInverse
  filter_upwards [finite] with sample bound
  have nonzero : ENNReal.ofReal (value sample) ≠ 0 := ENNReal.inv_ne_top.mp bound.ne
  exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr nonzero)

theorem orbitClusterSet_ae_positive_of_inverse_bound (measure : Measure Sample)
    {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]
    (sequence : ℕ → Lp ℝ exponent measure) (point : Lp ℝ exponent measure)
    (cluster : point ∈ orbitClusterSet sequence) (bound : ℝ≥0∞) (boundFinite : bound ≠ ∞)
    (bounds : ∀ depth, (∫⁻ sample, (ENNReal.ofReal (sequence depth sample))⁻¹ ∂measure) ≤ bound) :
    ∀ᵐ sample ∂measure, 0 < point sample := by
  have inherited := orbitClusterSet_lintegral_continuous_response_le measure sequence point cluster
    (fun value => (ENNReal.ofReal value)⁻¹) ENNReal.continuous_ofReal.fun_inv bound bounds
  exact ae_positive_of_lintegral_inverse_ofReal_lt_top measure point
    (Lp.aestronglyMeasurable _).aemeasurable (ne_top_of_le_ne_top boundFinite inherited)

end
end IGSIII.Chemical.SmallBall
