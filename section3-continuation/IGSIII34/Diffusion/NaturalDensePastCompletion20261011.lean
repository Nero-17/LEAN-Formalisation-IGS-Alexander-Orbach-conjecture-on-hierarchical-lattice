import IGSIII34.Diffusion.CountablePathMeasurableExtensionCompletion20261011
import Mathlib.Probability.Process.Filtration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Outcome Space : Type*} [MeasurableSpace Outcome]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

def countableDensePastTimeCompletion20261011 (times : ℕ → ℝ≥0) (present : ℝ≥0) : ℕ → ℝ≥0
  | 0 => present
  | index+1 => min present (times index)

theorem countableDensePastTime_before_completion20261011
    (times : ℕ → ℝ≥0) (present : ℝ≥0) (index : ℕ) :
    countableDensePastTimeCompletion20261011 times present index ≤ present := by
  cases index with
  | zero => exact le_rfl
  | succ index => exact min_le_left _ _

theorem countableDensePastTime_approximates_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (present time : ℝ≥0) (before : time ≤ present) :
    ∃ selected : ℕ → ℕ, Tendsto (fun index => countableDensePastTimeCompletion20261011 times present (selected index)) atTop (𝓝 time) := by
  let selected := fun index => countableTimeApproximatingIndexCompletion20261011 times dense time index + 1
  refine ⟨selected, ?_⟩
  have approximation := countableTimeApproximatingIndex_tendsto_completion20261011 times dense time
  have clampContinuous : Continuous (fun value : ℝ≥0 => min present value) := continuous_const.min continuous_id
  have clamped := (clampContinuous.tendsto time).comp approximation
  simpa only [selected, countableDensePastTimeCompletion20261011, min_eq_right before, Function.comp_def] using clamped

/-- Continuity of actual paths makes a countable dense past generate
the entire natural past sigma algebra, including the present time. -/
theorem countable_dense_past_generates_natural_completion20261011
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (sample : Outcome → ℝ≥0 → Space) (sampleContinuous : ∀ outcome, Continuous (sample outcome))
    (present : ℝ≥0) :
    MeasurableSpace.comap
      (fun outcome index => sample outcome (countableDensePastTimeCompletion20261011 times present index)) inferInstance =
      ⨆ time ≤ present, MeasurableSpace.comap (fun outcome => sample outcome time) inferInstance := by
  apply le_antisymm
  · rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro index
    exact le_iSup_of_le (countableDensePastTimeCompletion20261011 times present index)
      (le_iSup_of_le (countableDensePastTime_before_completion20261011 times present index) le_rfl)
  · apply iSup₂_le
    intro time before
    obtain ⟨selected, approximation⟩ := countableDensePastTime_approximates_completion20261011 times dense present time before
    let history := fun outcome index => sample outcome (countableDensePastTimeCompletion20261011 times present index)
    let historySigma := MeasurableSpace.comap history (inferInstance : MeasurableSpace (ℕ → Space))
    have measurableEvaluation : @Measurable Outcome Space historySigma inferInstance (fun outcome => sample outcome time) := by
      letI : MeasurableSpace Outcome := historySigma
      have historyMeasurable : Measurable history := Measurable.of_comap_le le_rfl
      have coordinateMeasurable (index : ℕ) : Measurable (fun outcome => history outcome (selected index)) :=
        (measurable_pi_apply (selected index)).comp historyMeasurable
      exact measurable_of_tendsto_metrizable coordinateMeasurable
        (tendsto_pi_nhds.mpr fun outcome => ((sampleContinuous outcome).tendsto time).comp approximation)
    exact measurableEvaluation.comap_le

end
end IGSIII34.Diffusion
