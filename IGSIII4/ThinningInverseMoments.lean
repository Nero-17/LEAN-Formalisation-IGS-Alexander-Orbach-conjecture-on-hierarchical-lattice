import IGSIII4.PositiveSmallBallStart

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory

theorem integrable_inv_pow_of_thinning_recursion_ae
    {Sample : Type*} [MeasurableSpace Sample] {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Sample → ℝ) (measurable : Measurable value)
    (positive : ∀ᵐ sample ∂measure, 0 < value sample)
    {critical base cutoff : ℝ} (power : ℕ)
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff)
    (initial : measure.real {sample | value sample ≤ cutoff} < 1)
    (step : ∀ depth : ℕ,
      measure.real {sample | value sample ≤ cutoff / base ^ (depth + 1)} ≤
        IGSIII34.Probability.thinningMap network critical
          (measure.real {sample | value sample ≤ cutoff / base ^ depth})) :
    Integrable (fun sample => (value sample)⁻¹ ^ power) measure := by
  let completed : Sample → ℝ := fun sample => if 0 < value sample then value sample else 1
  have completedMeasurable : Measurable completed :=
    Measurable.ite (measurableSet_lt measurable_const measurable) measurable measurable_const
  have completedPositive : ∀ sample, 0 < completed sample := by
    intro sample
    dsimp [completed]
    split_ifs with above
    · exact above
    · exact zero_lt_one
  have same : completed =ᵐ[measure] value := by
    filter_upwards [positive] with sample above
    simp only [completed, above, if_pos]
  have sameEvent (threshold : ℝ) :
      measure.real {sample | completed sample ≤ threshold} =
        measure.real {sample | value sample ≤ threshold} := by
    apply measureReal_congr
    filter_upwards [same] with sample equality
    change (completed sample ≤ threshold) = (value sample ≤ threshold)
    rw [equality]
  have completedIntegrable := IGSIII34.Probability.integrable_inv_pow_of_thinning_recursion network measure power
    completedMeasurable completedPositive criticalPositive criticalBelowOne fixedPoint scale
    (show 0 ≤ measure.real {sample | value sample ≤ cutoff} from measureReal_nonneg) initial
    baseAboveOne cutoffPositive (by rw [sameEvent])
    (fun depth => by simp only [sameEvent]; exact step depth)
  apply completedIntegrable.congr
  filter_upwards [same] with sample equality
  rw [equality]

end
end IGSIII4
