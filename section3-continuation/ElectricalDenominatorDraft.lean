import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

def electricalComparisonDenominator (value : ℝ) : ℝ := min (max value 0) (max 1 value)⁻¹

theorem electricalComparisonDenominator_continuous : Continuous electricalComparisonDenominator := by
  unfold electricalComparisonDenominator
  exact (continuous_id.max continuous_const).min ((continuous_const.max continuous_id).inv₀
    (fun value => (zero_lt_one.trans_le (le_max_left (1 : ℝ) value)).ne'))

theorem electricalComparisonDenominator_bounds (value : ℝ) :
    0 ≤ electricalComparisonDenominator value ∧ electricalComparisonDenominator value ≤ 1 := by
  unfold electricalComparisonDenominator
  have positive : 0 < max (1 : ℝ) value := zero_lt_one.trans_le (le_max_left _ _)
  exact ⟨le_min (le_max_right _ _) (inv_nonneg.mpr positive.le),
    (min_le_right _ _).trans ((inv_le_one₀ positive).mpr (le_max_left _ _))⟩

theorem electricalComparisonDenominator_eq (value : ℝ) (positive : 0 < value) :
    electricalComparisonDenominator value = min value value⁻¹ := by
  unfold electricalComparisonDenominator
  rw [max_eq_left positive.le]
  by_cases belowOne : value ≤ 1
  · rw [max_eq_left belowOne, inv_one, min_eq_left belowOne,
      min_eq_left (belowOne.trans ((one_le_inv₀ positive).mpr belowOne))]
  · rw [max_eq_right (le_of_not_ge belowOne)]

theorem lp2_integral_bounded_continuous_tendsto
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (sequence : ℕ → Lp ℝ 2 measure) (limit : Lp ℝ 2 measure)
    (convergence : Tendsto sequence atTop (𝓝 limit)) (test : ℝ → ℝ) (continuous : Continuous test)
    (bound : ℝ) (bounded : ∀ value, ‖test value‖ ≤ bound) :
    Tendsto (fun depth => ∫ sample, test (sequence depth sample) ∂measure) atTop
      (𝓝 (∫ sample, test (limit sample) ∂measure)) := by
  apply tendsto_of_subseq_tendsto
  intro subsequence indicesTendsto
  obtain ⟨subsubsequence, _, pointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (convergence.comp indicesTendsto)).exists_seq_tendsto_ae
  refine ⟨subsubsequence, ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun _ => bound)
    (fun depth => (continuous.measurable.comp (Lp.stronglyMeasurable (sequence (subsequence (subsubsequence depth)))).measurable).aestronglyMeasurable)
    (integrable_const bound) (fun depth => Filter.Eventually.of_forall (fun sample => bounded _))
  filter_upwards [pointwise] with sample limitEquality
  exact continuous.continuousAt.tendsto.comp limitEquality

theorem electrical_comparison_denominator_tendsto
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (sequence : ℕ → Lp ℝ 2 measure) (limit : Lp ℝ 2 measure)
    (convergence : Tendsto sequence atTop (𝓝 limit))
    (sequencePositive : ∀ depth, ∀ᵐ sample ∂measure, 0 < sequence depth sample)
    (limitPositive : ∀ᵐ sample ∂measure, 0 < limit sample) :
    Tendsto (fun depth => ∫ sample, min (sequence depth sample) (sequence depth sample)⁻¹ ∂measure) atTop
      (𝓝 (∫ sample, min (limit sample) (limit sample)⁻¹ ∂measure)) := by
  have convergence := lp2_integral_bounded_continuous_tendsto measure sequence limit convergence
    electricalComparisonDenominator electricalComparisonDenominator_continuous 1 (fun value => by
      rw [Real.norm_eq_abs, abs_of_nonneg (electricalComparisonDenominator_bounds value).1]
      exact (electricalComparisonDenominator_bounds value).2)
  have sequenceEquality (depth : ℕ) : (∫ sample, electricalComparisonDenominator (sequence depth sample) ∂measure) =
      ∫ sample, min (sequence depth sample) (sequence depth sample)⁻¹ ∂measure :=
    integral_congr_ae ((sequencePositive depth).mono (fun _ positive => electricalComparisonDenominator_eq _ positive))
  have limitEquality : (∫ sample, electricalComparisonDenominator (limit sample) ∂measure) =
      ∫ sample, min (limit sample) (limit sample)⁻¹ ∂measure :=
    integral_congr_ae (limitPositive.mono (fun _ positive => electricalComparisonDenominator_eq _ positive))
  simpa only [sequenceEquality, limitEquality] using convergence

theorem electrical_comparison_denominator_mean_positive
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Lp ℝ 2 measure) (positive : ∀ᵐ sample ∂measure, 0 < value sample) :
    0 < ∫ sample, min (value sample) (value sample)⁻¹ ∂measure := by
  have integrable : Integrable (fun sample => min (value sample) (value sample)⁻¹) measure := by
    apply ((Lp.memLp value).integrable (by norm_num)).mono'
      ((Lp.stronglyMeasurable value).measurable.min (Lp.stronglyMeasurable value).measurable.inv).aestronglyMeasurable
    filter_upwards [positive] with sample valuePositive
    change |min (value sample) (value sample)⁻¹| ≤ value sample
    rw [abs_of_nonneg (le_min valuePositive.le (inv_pos.mpr valuePositive).le)]
    exact min_le_left _ _
  have positive : ∀ᵐ sample ∂measure, 0 < min (value sample) (value sample)⁻¹ :=
    positive.mono (fun _ inequality => lt_min inequality (inv_pos.mpr inequality))
  apply (integral_pos_iff_support_of_nonneg_ae (positive.mono (fun _ inequality => inequality.le)) integrable).mpr
  have supportEquality : Function.support (fun sample => min (value sample) (value sample)⁻¹) =ᵐ[measure] Set.univ := by
    filter_upwards [positive] with sample inequality
    change (min (value sample) (value sample)⁻¹ ≠ 0) = True
    exact propext (iff_true_intro inequality.ne')
  rw [measure_congr supportEquality, measure_univ]
  exact zero_lt_one

end
end IGSIII34.Probability

