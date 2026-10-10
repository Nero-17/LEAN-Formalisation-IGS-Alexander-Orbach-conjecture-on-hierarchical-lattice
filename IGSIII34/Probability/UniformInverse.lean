import IGSIII34.Probability.AEInverse
import IGSIII.Chemical.SmallBall.UniformMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Universality

theorem inverse_moment_of_uniform_thinning_tail_ae
    {Sample : Type*} [MeasurableSpace Sample]
    {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {value : Sample → ℝ} {critical start base cutoff : ℝ} (power : ℕ)
    (measurable : Measurable value) (positive : ∀ᵐ sample ∂measure, 0 < value sample)
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff)
    (tailBound : ∀ depth : ℕ,
      measure.real {sample | value sample ≤ cutoff / base ^ depth} ≤
        (thinningMap network critical)^[depth] start) :
    Integrable (fun sample => (value sample)⁻¹ ^ power) measure ∧
      (∫ sample, (value sample)⁻¹ ^ power ∂measure) ≤
        cutoff⁻¹ ^ power * (1 + base ^ power *
          ∑' depth : ℕ, (base ^ power) ^ depth * (thinningMap network critical)^[depth] start) := by
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
  have representativeTail (depth : ℕ) :
      measure.real {sample | representative sample ≤ cutoff / base ^ depth} ≤
        (thinningMap network critical)^[depth] start := by
    rw [eventEquality]
    exact tailBound depth
  have summability := thinningMap_weighted_iterate_summable network criticalPositive criticalBelowOne
    fixedPoint scale startNonnegative startBelowOne (pow_pos (zero_lt_one.trans baseAboveOne) power)
  have representativeIntegrable := integrable_inv_pow_of_summable_smallBall measure power
    representativeMeasurable representativePositive baseAboveOne cutoffPositive
    (Summable.of_nonneg_of_le
      (fun depth => mul_nonneg (pow_nonneg (pow_nonneg (zero_lt_one.trans baseAboveOne).le power) depth) measureReal_nonneg)
      (fun depth => mul_le_mul_of_nonneg_left (representativeTail depth)
        (pow_nonneg (pow_nonneg (zero_lt_one.trans baseAboveOne).le power) depth)) summability)
  have inverseEquality : (fun sample => (representative sample)⁻¹ ^ power) =ᵐ[measure]
      (fun sample => (value sample)⁻¹ ^ power) := by
    filter_upwards [representativeEquality] with sample equality
    rw [equality]
  refine ⟨representativeIntegrable.congr inverseEquality, ?_⟩
  rw [← integral_congr_ae inverseEquality]
  have mapsEqual : IGSIII.Chemical.SmallBall.thinningMap network critical = thinningMap network critical := rfl
  have estimate := IGSIII.Chemical.SmallBall.integral_inv_pow_le_of_thinning_tail_bound
    network measure power representativeMeasurable representativePositive criticalPositive criticalBelowOne
    fixedPoint scale startNonnegative startBelowOne baseAboveOne cutoffPositive
    (fun depth => by
      rw [mapsEqual]
      exact representativeTail depth)
  rwa [mapsEqual] at estimate

end
end IGSIII34.Probability
