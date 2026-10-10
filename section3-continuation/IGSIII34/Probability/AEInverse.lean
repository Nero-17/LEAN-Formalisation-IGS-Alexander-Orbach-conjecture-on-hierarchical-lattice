import IGSIII34.Probability.InverseMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory

theorem integrable_inv_pow_of_thinning_recursion_ae
    {Sample : Type*} [MeasurableSpace Sample]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {value : Sample → ℝ} {critical start base cutoff : ℝ} (power : ℕ)
    (measurable : Measurable value) (positive : ∀ᵐ sample ∂measure, 0 < value sample)
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff)
    (initial : measure.real {sample | value sample ≤ cutoff} ≤ start)
    (step : ∀ depth : ℕ,
      measure.real {sample | value sample ≤ cutoff / base ^ (depth + 1)} ≤
        thinningMap network critical
          (measure.real {sample | value sample ≤ cutoff / base ^ depth})) :
    Integrable (fun sample => (value sample)⁻¹ ^ power) measure := by
  let representative : Sample → ℝ := fun sample => if 0 < value sample then value sample else 1
  have representativeMeasurable : Measurable representative :=
    measurable.ite (measurableSet_lt measurable_const measurable) measurable_const
  have representativePositive (sample : Sample) : 0 < representative sample := by
    dsimp [representative]
    split_ifs with positive
    · exact positive
    · exact zero_lt_one
  have representativeEquality : representative =ᵐ[measure] value := by
    filter_upwards [positive] with sample positive
    exact if_pos positive
  have eventEquality (threshold : ℝ) :
      measure.real {sample | representative sample ≤ threshold} =
        measure.real {sample | value sample ≤ threshold} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [representativeEquality] with sample equality
    exact congrArg (fun result : ℝ => result ≤ threshold) equality
  have result := integrable_inv_pow_of_thinning_recursion network measure power
    representativeMeasurable representativePositive criticalPositive criticalBelowOne fixedPoint scale
    startNonnegative startBelowOne baseAboveOne cutoffPositive
    ((eventEquality cutoff).trans_le initial)
    (fun depth => by simpa only [eventEquality] using step depth)
  apply result.congr
  filter_upwards [representativeEquality] with sample equality
  rw [equality]

end
end IGSIII34.Probability
