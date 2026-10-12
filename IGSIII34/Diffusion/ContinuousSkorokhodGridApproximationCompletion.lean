import IGSIII34.Diffusion.SkorokhodRegularGridCompletion
import IGSIII34.Diffusion.SkorokhodContinuousSampleCompletion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def continuousSkorokhodRegularReconstructionCompletion (grid : ℕ)
    (path : C(SkorokhodIntervalTimeCompletion, Space)) : SkorokhodIntervalPathCompletion Space :=
  skorokhodFiniteReconstructionCompletion (skorokhodRegularGridSelectionCompletion grid)
    (fun index => path (skorokhodRegularGridPointCompletion grid index))

theorem continuousSkorokhodRegularReconstruction_continuous_completion (grid : ℕ) :
    Continuous (continuousSkorokhodRegularReconstructionCompletion (Space := Space) grid) :=
  (skorokhodFiniteReconstruction_lipschitz_completion _).continuous.comp
    (continuous_pi fun index => continuous_eval_const _)

theorem continuousSkorokhodRegular_error_continuous_completion (grid : ℕ) :
    Continuous (fun path : C(SkorokhodIntervalTimeCompletion, Space) =>
      dist (continuousIntervalPathCompletion path) (continuousSkorokhodRegularReconstructionCompletion grid path)) :=
  continuousIntervalPath_lipschitz_completion.continuous.dist
    (continuousSkorokhodRegularReconstruction_continuous_completion grid)

/-- Every continuous interval path is genuinely approximated in the J1
time-change metric by its finite regular-grid observations. -/
theorem continuousSkorokhodRegular_error_tendsto_completion
    (path : C(SkorokhodIntervalTimeCompletion, Space)) :
    Tendsto (fun grid => dist (continuousIntervalPathCompletion path)
      (continuousSkorokhodRegularReconstructionCompletion grid path)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  obtain ⟨duration, durationPositive, uniform⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous path.continuous) (tolerance / 2) (by positivity)
  filter_upwards [skorokhodRegularGrid_mesh_tendsto_completion.eventually (gt_mem_nhds durationPositive)] with grid mesh
  have edistance := skorokhod_reconstruction_modulus_bound_completion
    (skorokhodRegularGridPointCompletion grid) (skorokhodRegularGridSelectionCompletion grid)
    (continuousIntervalPathCompletion path) duration (tolerance / 2)
    (fun time => (skorokhodRegularGridSelection_near_completion grid time).trans mesh)
    (fun first second close => (uniform close).le)
  have distanceBound := (edist_le_ofReal (by positivity : 0 ≤ tolerance / 2)).mp edistance
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  exact distanceBound.trans_lt (by linarith)

theorem continuousSkorokhodRegular_bad_probability_tendsto_completion
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → C(SkorokhodIntervalTimeCompletion, Space))
    (sampleMeasurable : letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _; Measurable sample)
    (tolerance : ℝ) (positive : 0 < tolerance) :
    Tendsto (fun grid => law.real {outcome | tolerance <
      dist (continuousIntervalPathCompletion (sample outcome))
        (continuousSkorokhodRegularReconstructionCompletion grid (sample outcome))}) atTop (𝓝 0) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion, Space) := ⟨rfl⟩
  let bad := fun grid => {outcome | tolerance <
    dist (continuousIntervalPathCompletion (sample outcome))
      (continuousSkorokhodRegularReconstructionCompletion grid (sample outcome))}
  have badMeasurable (grid : ℕ) : MeasurableSet (bad grid) :=
    measurableSet_lt measurable_const ((continuousSkorokhodRegular_error_continuous_completion grid).measurable.comp sampleMeasurable)
  have dominated := tendsto_integral_of_dominated_convergence (μ := law)
    (F := fun grid => (bad grid).indicator (fun _ : Outcome => (1 : ℝ))) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun grid => (measurable_const.indicator (badMeasurable grid)).aestronglyMeasurable)
    (integrable_const 1)
    (fun grid => Eventually.of_forall fun outcome => by
      by_cases belongs : outcome ∈ bad grid
      · rw [Set.indicator_of_mem belongs]; norm_num
      · rw [Set.indicator_of_notMem belongs]; norm_num)
    (Eventually.of_forall fun outcome => by
      have eventuallyGood := (continuousSkorokhodRegular_error_tendsto_completion (sample outcome)).eventually (gt_mem_nhds positive)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventuallyGood] with grid close
      have notBad : outcome ∉ bad grid := not_lt.mpr close.le
      simp only [Set.indicator_of_notMem notBad])
  simpa only [integral_indicator_const (1 : ℝ) (badMeasurable _), smul_eq_mul, mul_one, integral_zero, bad] using dominated

end
end IGSIII34.Diffusion




