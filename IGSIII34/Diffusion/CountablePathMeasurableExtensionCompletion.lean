import IGSIII34.Diffusion.CountablePathExtensionCompletion
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

theorem countableTimeLocalUniform_countable_iff_completion
    (times : ℕ → ℝ≥0) (path : ℕ → Space) :
    countableTimeLocalUniformContinuityCompletion times path ↔
      ∀ horizon tolerance : ℕ, ∃ duration : ℕ, ∀ first last : ℕ,
        ((times first : ℝ) ≤ horizon ∧ (times last : ℝ) ≤ horizon ∧
          dist (times first) (times last) < 1 / (duration + 1 : ℝ)) →
            dist (path first) (path last) ≤ 1 / (tolerance + 1 : ℝ) := by
  constructor
  · intro regular horizon tolerance
    obtain ⟨duration, durationPositive, close⟩ := regular horizon (1 / (tolerance + 1 : ℝ)) (by positivity)
    have eventuallySmall : ∀ᶠ index : ℕ in atTop, 1 / (index + 1 : ℝ) < duration :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds durationPositive)
    obtain ⟨index, small⟩ := eventuallySmall.exists
    exact ⟨index, fun first last member =>
      (close first last member.1 member.2.1 (member.2.2.trans small)).le⟩
  · intro countable horizon tolerance tolerancePositive
    have eventuallySmall : ∀ᶠ index : ℕ in atTop, 1 / (index + 1 : ℝ) < tolerance :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds tolerancePositive)
    obtain ⟨index, small⟩ := eventuallySmall.exists
    obtain ⟨duration, close⟩ := countable horizon index
    exact ⟨1 / (duration + 1 : ℝ), by positivity, fun first last beforeFirst beforeLast near =>
      (close first last ⟨beforeFirst, beforeLast, near⟩).trans_lt small⟩

theorem countableTimeLocalUniform_measurableSet_completion (times : ℕ → ℝ≥0) :
    MeasurableSet {path : ℕ → Space | countableTimeLocalUniformContinuityCompletion times path} := by
  have measurableCountable : MeasurableSet {path : ℕ → Space |
      ∀ horizon tolerance : ℕ, ∃ duration : ℕ, ∀ first last : ℕ,
        ((times first : ℝ) ≤ horizon ∧ (times last : ℝ) ≤ horizon ∧
          dist (times first) (times last) < 1 / (duration + 1 : ℝ)) →
            dist (path first) (path last) ≤ 1 / (tolerance + 1 : ℝ)} := by
    simp only [setOf_forall, setOf_exists]
    exact MeasurableSet.iInter fun horizon => MeasurableSet.iInter fun tolerance =>
      MeasurableSet.iUnion fun duration => MeasurableSet.iInter fun first => MeasurableSet.iInter fun last =>
        MeasurableSet.iInter fun _condition => measurableSet_le
          ((show Continuous (fun path : ℕ → Space => dist (path first) (path last)) from by fun_prop).measurable)
          measurable_const
  convert measurableCountable using 1
  ext path
  exact countableTimeLocalUniform_countable_iff_completion times path

def countableTimeApproximatingIndexCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (time : ℝ≥0) (index : ℕ) : ℕ :=
  Classical.choose (dense.exists_dist_lt time (show 0 < 1 / (index + 1 : ℝ) by positivity))

theorem countableTimeApproximatingIndex_tendsto_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (time : ℝ≥0) :
    Tendsto (fun index => times (countableTimeApproximatingIndexCompletion times dense time index)) atTop (𝓝 time) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds positive)] with index small
  rw [dist_comm]
  exact (Classical.choose_spec (dense.exists_dist_lt time (show 0 < 1 / (index + 1 : ℝ) by positivity))).trans small

def countableTimeContinuousSampleCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (path : ℕ → Space) : ℝ≥0 → Space := by
  classical
  exact if countableTimeLocalUniformContinuityCompletion times path then
    countableTimeContinuousExtensionCompletion times path else fun _ => path 0

theorem countableTimeContinuousSample_continuous_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (path : ℕ → Space) :
    Continuous (countableTimeContinuousSampleCompletion times dense path) := by
  classical
  by_cases regular : countableTimeLocalUniformContinuityCompletion times path
  · rw [countableTimeContinuousSampleCompletion, if_pos regular]
    exact (countableTimeContinuousExtension_properties_completion times dense path regular).1
  · rw [countableTimeContinuousSampleCompletion, if_neg regular]
    exact continuous_const

theorem countableTimeContinuousSample_evaluation_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (time : ℝ≥0) :
    Measurable (fun path : ℕ → Space => countableTimeContinuousSampleCompletion times dense path time) := by
  classical
  let approximating (index : ℕ) (path : ℕ → Space) :=
    if countableTimeLocalUniformContinuityCompletion times path then
      path (countableTimeApproximatingIndexCompletion times dense time index) else path 0
  have measurableApprox (index : ℕ) : Measurable (approximating index) :=
    Measurable.ite (countableTimeLocalUniform_measurableSet_completion times)
      (measurable_pi_apply _) (measurable_pi_apply 0)
  apply measurable_of_tendsto_metrizable measurableApprox
  apply tendsto_pi_nhds.mpr
  intro path
  by_cases regular : countableTimeLocalUniformContinuityCompletion times path
  · have properties := countableTimeContinuousExtension_properties_completion times dense path regular
    have converges := (properties.1.tendsto time).comp (countableTimeApproximatingIndex_tendsto_completion times dense time)
    simpa only [approximating, if_pos regular, countableTimeContinuousSampleCompletion,
      Function.comp_def, properties.2] using converges
  · simpa only [approximating, if_neg regular, countableTimeContinuousSampleCompletion] using
      (tendsto_const_nhds : Tendsto (fun _index : ℕ => path 0) atTop (𝓝 (path 0)))

theorem countableTimeContinuousSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableTimeContinuousSampleCompletion (Space := Space) times dense) :=
  measurable_pi_lambda _ (fun time => countableTimeContinuousSample_evaluation_measurable_completion times dense time)

/-- The continuous process lives on the genuine countable-time sample
space; one common measurable null-set repair preserves its entire sample
path and all observed coordinates simultaneously. -/
theorem countableTimeContinuousSample_ae_agreement_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (law : ProbabilityMeasure (ℕ → Space))
    (regular : ∀ᵐ path ∂(law : Measure (ℕ → Space)), countableTimeLocalUniformContinuityCompletion times path) :
    ∀ᵐ path ∂(law : Measure (ℕ → Space)), ∀ coordinate,
      countableTimeContinuousSampleCompletion times dense path (times coordinate) = path coordinate := by
  classical
  filter_upwards [regular] with path good
  rw [countableTimeContinuousSampleCompletion, if_pos good]
  exact (countableTimeContinuousExtension_properties_completion times dense path good).2

end
end IGSIII34.Diffusion
