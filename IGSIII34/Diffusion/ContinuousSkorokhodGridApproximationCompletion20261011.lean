import IGSIII34.Diffusion.SkorokhodRegularGridCompletion20261011
import IGSIII34.Diffusion.SkorokhodContinuousSampleCompletion20261011
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def continuousSkorokhodRegularReconstructionCompletion20261011 (grid : ℕ)
    (path : C(SkorokhodIntervalTimeCompletion20261011, Space)) : SkorokhodIntervalPathCompletion20261011 Space :=
  skorokhodFiniteReconstructionCompletion20261011 (skorokhodRegularGridSelectionCompletion20261011 grid)
    (fun index => path (skorokhodRegularGridPointCompletion20261011 grid index))

theorem continuousSkorokhodRegularReconstruction_continuous_completion20261011 (grid : ℕ) :
    Continuous (continuousSkorokhodRegularReconstructionCompletion20261011 (Space := Space) grid) :=
  (skorokhodFiniteReconstruction_lipschitz_completion20261011 _).continuous.comp
    (continuous_pi fun index => continuous_eval_const _)

theorem continuousSkorokhodRegular_error_continuous_completion20261011 (grid : ℕ) :
    Continuous (fun path : C(SkorokhodIntervalTimeCompletion20261011, Space) =>
      dist (continuousIntervalPathCompletion20261011 path) (continuousSkorokhodRegularReconstructionCompletion20261011 grid path)) :=
  continuousIntervalPath_lipschitz_completion20261011.continuous.dist
    (continuousSkorokhodRegularReconstruction_continuous_completion20261011 grid)

/-- Every continuous interval path is genuinely approximated in the J1
time-change metric by its finite regular-grid observations. -/
theorem continuousSkorokhodRegular_error_tendsto_completion20261011
    (path : C(SkorokhodIntervalTimeCompletion20261011, Space)) :
    Tendsto (fun grid => dist (continuousIntervalPathCompletion20261011 path)
      (continuousSkorokhodRegularReconstructionCompletion20261011 grid path)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  obtain ⟨duration, durationPositive, uniform⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous path.continuous) (tolerance / 2) (by positivity)
  filter_upwards [skorokhodRegularGrid_mesh_tendsto_completion20261011.eventually (gt_mem_nhds durationPositive)] with grid mesh
  have edistance := skorokhod_reconstruction_modulus_bound_completion20261011
    (skorokhodRegularGridPointCompletion20261011 grid) (skorokhodRegularGridSelectionCompletion20261011 grid)
    (continuousIntervalPathCompletion20261011 path) duration (tolerance / 2)
    (fun time => (skorokhodRegularGridSelection_near_completion20261011 grid time).trans mesh)
    (fun first second close => (uniform close).le)
  have distanceBound := (edist_le_ofReal (by positivity : 0 ≤ tolerance / 2)).mp edistance
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  exact distanceBound.trans_lt (by linarith)

theorem continuousSkorokhodRegular_bad_probability_tendsto_completion20261011
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → C(SkorokhodIntervalTimeCompletion20261011, Space))
    (sampleMeasurable : letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := borel _; Measurable sample)
    (tolerance : ℝ) (positive : 0 < tolerance) :
    Tendsto (fun grid => law.real {outcome | tolerance <
      dist (continuousIntervalPathCompletion20261011 (sample outcome))
        (continuousSkorokhodRegularReconstructionCompletion20261011 grid (sample outcome))}) atTop (𝓝 0) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := ⟨rfl⟩
  let bad := fun grid => {outcome | tolerance <
    dist (continuousIntervalPathCompletion20261011 (sample outcome))
      (continuousSkorokhodRegularReconstructionCompletion20261011 grid (sample outcome))}
  have badMeasurable (grid : ℕ) : MeasurableSet (bad grid) :=
    measurableSet_lt measurable_const ((continuousSkorokhodRegular_error_continuous_completion20261011 grid).measurable.comp sampleMeasurable)
  have dominated := tendsto_integral_of_dominated_convergence (μ := law)
    (F := fun grid => (bad grid).indicator (fun _ : Outcome => (1 : ℝ))) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun grid => (measurable_const.indicator (badMeasurable grid)).aestronglyMeasurable)
    (integrable_const 1)
    (fun grid => Eventually.of_forall fun outcome => by
      by_cases belongs : outcome ∈ bad grid
      · rw [Set.indicator_of_mem belongs]; norm_num
      · rw [Set.indicator_of_notMem belongs]; norm_num)
    (Eventually.of_forall fun outcome => by
      have eventuallyGood := (continuousSkorokhodRegular_error_tendsto_completion20261011 (sample outcome)).eventually (gt_mem_nhds positive)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventuallyGood] with grid close
      have notBad : outcome ∉ bad grid := not_lt.mpr close.le
      simp only [Set.indicator_of_notMem notBad])
  simpa only [integral_indicator_const (1 : ℝ) (badMeasurable _), smul_eq_mul, mul_one, integral_zero, bad] using dominated

end
end IGSIII34.Diffusion




