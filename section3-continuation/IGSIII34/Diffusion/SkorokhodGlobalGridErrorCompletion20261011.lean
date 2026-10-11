import IGSIII34.Diffusion.SkorokhodGlobalRegularGridCompletion20261011
import IGSIII34.Diffusion.SkorokhodGlobalContinuousSampleCompletion20261011
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

theorem skorokhodGlobalContinuousAssembly_evaluation_continuous_completion20261011 (time : ℝ≥0) :
    Continuous (fun profiles : ℕ → C(SkorokhodIntervalTimeCompletion20261011, Space) =>
      skorokhodGlobalContinuousAssemblyCompletion20261011 profiles time) :=
  (continuous_eval_const (skorokhodGlobalUnitCoordinateCompletion20261011 time)).comp
    (continuous_apply ⌊(time : ℝ)⌋₊)

theorem skorokhodGlobalContinuousAssembly_grid_error_continuous_completion20261011 (horizon grid : ℕ) :
    Continuous (fun profiles : ℕ → C(SkorokhodIntervalTimeCompletion20261011, Space) =>
      dist (skorokhodGlobalContinuousAssemblyCompletion20261011 profiles)
        (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid
          (skorokhodGlobalContinuousAssemblyCompletion20261011 profiles))) :=
  skorokhodGlobalContinuousAssembly_continuous_completion20261011.dist
    ((skorokhodGlobalFiniteReconstruction_continuous_completion20261011 _).comp
      (continuous_pi fun index => skorokhodGlobalContinuousAssembly_evaluation_continuous_completion20261011
        (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid index)))

theorem continuousGlobal_grid_error_measurable_completion20261011
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sample : Outcome → ℝ≥0 → Space) (sampleContinuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) (horizon grid : ℕ) :
    Measurable (fun outcome => dist (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space)
      (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid ⟨sample outcome⟩)) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := ⟨rfl⟩
  let profiles : Outcome → ℕ → C(SkorokhodIntervalTimeCompletion20261011, Space) := fun outcome horizon =>
    ⟨fun time => sample outcome ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩),
      (sampleContinuous outcome).comp (by fun_prop)⟩
  have profilesMeasurable : Measurable profiles := by
    apply measurable_pi_lambda
    intro index
    apply continuousIntervalFamily_measurable_of_evaluations_completion20261011
    intro time
    exact evaluations ((index+1 : ℝ≥0) * ⟨time.val, time.property.1⟩)
  have identity (outcome : Outcome) : skorokhodGlobalContinuousAssemblyCompletion20261011 (profiles outcome) =
      (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space) := by
    apply congrArg SkorokhodGlobalPathCompletion20261011.mk
    funext time
    change sample outcome ((⌊(time : ℝ)⌋₊ + 1 : ℝ≥0) *
      ⟨(time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ), _⟩) = sample outcome time
    congr 1
    apply NNReal.eq
    change (⌊(time : ℝ)⌋₊ + 1 : ℝ) * ((time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ)) = (time : ℝ)
    exact mul_div_cancel₀ _ (by positivity : (⌊(time : ℝ)⌋₊ + 1 : ℝ) ≠ 0)
  convert (skorokhodGlobalContinuousAssembly_grid_error_continuous_completion20261011 (Space := Space)
    horizon grid).measurable.comp profilesMeasurable using 1
  funext outcome
  dsimp only [Function.comp_apply]
  rw [identity]

theorem continuousGlobal_regular_grid_eventually_close_completion20261011
    (path : ℝ≥0 → Space) (pathContinuous : Continuous path) (horizon : ℕ)
    (tolerance : ℝ) (tail : 2 * (2 : ℝ)⁻¹ ^ (horizon+1) < tolerance) :
    ∀ᶠ grid : ℕ in atTop,
      dist (⟨path⟩ : SkorokhodGlobalPathCompletion20261011 Space)
        (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid ⟨path⟩) < tolerance := by
  let error := (tolerance - 2 * (2 : ℝ)⁻¹ ^ (horizon+1)) / (2 * (horizon+1 : ℝ))
  have errorPositive : 0 < error := by dsimp [error]; positivity
  have compactUniform := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) (horizon+1))).uniformContinuousOn_of_continuous pathContinuous.continuousOn
  obtain ⟨duration, durationPositive, uniform⟩ := Metric.uniformContinuousOn_iff.mp compactUniform error errorPositive
  have mesh : Tendsto (fun grid : ℕ => (horizon+1 : ℝ) / (grid+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using (skorokhodRegularGrid_mesh_tendsto_completion20261011.const_mul (horizon+1 : ℝ))
  filter_upwards [mesh.eventually (gt_mem_nhds durationPositive)] with grid meshSmall
  have profiles (index : ℕ) (before : index < horizon+1) :=
    skorokhodGlobalRegularReconstruction_profile_bound_completion20261011 horizon grid ⟨path⟩
      duration error errorPositive.le meshSmall
      (fun first second firstBefore secondBefore close =>
        (uniform first ⟨zero_le, firstBefore⟩ second ⟨zero_le, secondBefore⟩ close).le)
      index (Nat.le_of_lt_succ before)
  have bound := skorokhodGlobal_dist_finite_profile_bound_completion20261011 ⟨path⟩
    (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid ⟨path⟩) (horizon+1) error profiles
  have identity : 2 * (horizon+1 : ℝ) * error = tolerance - 2 * (2 : ℝ)⁻¹ ^ (horizon+1) := by
    dsimp [error]
    field_simp
  have castCount : ((horizon+1 : ℕ) : ℝ) = (horizon+1 : ℝ) := by norm_cast
  rw [castCount] at bound
  linarith

theorem continuousGlobal_regular_grid_bad_probability_tendsto_completion20261011
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → ℝ≥0 → Space) (sampleContinuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (horizon : ℕ) (tolerance : ℝ) (tail : 2 * (2 : ℝ)⁻¹ ^ (horizon+1) < tolerance) :
    Tendsto (fun grid => law.real {outcome | tolerance <
      dist (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space)
        (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid ⟨sample outcome⟩)}) atTop (𝓝 0) := by
  let bad := fun grid => {outcome | tolerance <
    dist (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space)
      (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid ⟨sample outcome⟩)}
  have badMeasurable (grid : ℕ) : MeasurableSet (bad grid) := measurableSet_lt measurable_const
    (continuousGlobal_grid_error_measurable_completion20261011 sample sampleContinuous evaluations horizon grid)
  have dominated := tendsto_integral_of_dominated_convergence (μ := law)
    (F := fun grid => (bad grid).indicator (fun _ : Outcome => (1 : ℝ))) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun grid => (measurable_const.indicator (badMeasurable grid)).aestronglyMeasurable)
    (integrable_const 1)
    (fun grid => Eventually.of_forall fun outcome => by
      by_cases belongs : outcome ∈ bad grid
      · rw [Set.indicator_of_mem belongs]; norm_num
      · rw [Set.indicator_of_notMem belongs]; norm_num)
    (Eventually.of_forall fun outcome => by
      have eventuallyGood := continuousGlobal_regular_grid_eventually_close_completion20261011
        (sample outcome) (sampleContinuous outcome) horizon tolerance tail
      apply tendsto_const_nhds.congr'
      filter_upwards [eventuallyGood] with grid close
      have notBad : outcome ∉ bad grid := not_lt.mpr close.le
      simp only [Set.indicator_of_notMem notBad])
  simpa only [integral_indicator_const (1 : ℝ) (badMeasurable _), smul_eq_mul, mul_one, integral_zero, bad] using dominated

end
end IGSIII34.Diffusion
