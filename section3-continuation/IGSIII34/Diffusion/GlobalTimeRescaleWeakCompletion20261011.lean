import IGSIII34.Diffusion.GlobalTimeRescaleCouplingCompletion20261011
import IGSIII34.Diffusion.SkorokhodGlobalAEWeakConvergenceCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space Outcome : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [MeasurableSpace Outcome]

theorem skorokhodGlobal_fixed_time_scale_weak_completion20261011
    {Samples : ℕ → Type*} [∀ index, MeasurableSpace (Samples index)]
    (laws : ∀ index, Measure (Samples index)) [∀ index, IsProbabilityMeasure (laws index)]
    (samples : ∀ index, Samples index → SkorokhodGlobalPathCompletion20261011 Space)
    (evaluations : ∀ index time, Measurable (fun outcome => samples index outcome time))
    (scale : ℝ≥0)
    (samplesMeasurable : ∀ index, AEMeasurable
      (fun outcome => skorokhodGlobalTimeScaleCompletion20261011 scale (samples index outcome)) (laws index))
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → ℝ≥0 → Space) (continuous : ∀ outcome, Continuous (sample outcome))
    (limitEvaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (finiteMarginals : ∀ count (futureTimes : Fin count → ℝ≥0),
      Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
        ((measurable_pi_lambda _ fun coordinate => evaluations index (futureTimes coordinate)).aemeasurable)) atTop
        (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
          ((measurable_pi_lambda _ fun coordinate => limitEvaluations (futureTimes coordinate)).aemeasurable))))
    (modulus : ∀ horizon : ℝ≥0, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ index in atTop,
        ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
          ∀ outcome ∉ bad, ∀ first second : ℝ≥0, first ≤ horizon → second ≤ horizon →
            dist first second < duration → dist (samples index outcome first) (samples index outcome second) ≤ tolerance) :
    Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
      (samplesMeasurable index)) atTop
      (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
        (continuousGlobalFamily_measurable_completion20261011
          (fun outcome time => sample outcome (scale*time))
          (fun outcome => (continuous outcome).comp (continuous_const.mul continuous_id))
          (fun time => limitEvaluations (scale*time))).aemeasurable)) := by
  apply skorokhodGlobal_ae_weak_of_finite_marginals_and_modulus_completion20261011 Samples laws
    (fun index outcome => skorokhodGlobalTimeScaleCompletion20261011 scale (samples index outcome)) samplesMeasurable
    (fun index time => evaluations index (scale*time)) law
    (fun outcome time => sample outcome (scale*time))
    (fun outcome => (continuous outcome).comp (continuous_const.mul continuous_id))
    (fun time => limitEvaluations (scale*time))
  · intro horizon grid
    exact finiteMarginals (grid+2) (fun coordinate => scale * skorokhodGlobalRegularGridPointCompletion20261011 horizon grid coordinate)
  · intro horizon tolerance error tolerancePositive errorPositive
    obtain ⟨duration, durationPositive, probabilities⟩ := modulus (scale*(horizon+1)) tolerance error tolerancePositive errorPositive
    refine ⟨duration/((scale:ℝ)+1), by positivity, ?_⟩
    filter_upwards [probabilities] with index probability
    obtain ⟨bad, badMeasurable, badProbability, good⟩ := probability
    refine ⟨bad, badMeasurable, badProbability, ?_⟩
    intro outcome outside first second firstBound secondBound near
    apply good outcome outside (scale*first) (scale*second)
      (mul_le_mul_of_nonneg_left firstBound (by positivity))
      (mul_le_mul_of_nonneg_left secondBound (by positivity))
    have identity : dist (scale*first) (scale*second) = (scale:ℝ)*dist first second := by
      change |(scale:ℝ)*(first:ℝ)-(scale:ℝ)*(second:ℝ)| = (scale:ℝ) * |(first:ℝ)-(second:ℝ)|
      rw [← mul_sub, abs_mul]
      congr 1
      exact NNReal.abs_eq scale
    rw [identity]
    have bound := (lt_div_iff₀ (by positivity : 0 < (scale:ℝ)+1)).mp near
    nlinarith [dist_nonneg (x := first) (y := second), scale.property]

/-- Converging positive deterministic clock ratios preserve the whole
path limit and rescale the limiting continuous process. This establishes
the process content of deterministic-clock corollaries, rather than only
the numerical asymptotic clock ratio. -/
theorem skorokhodGlobal_varying_time_scale_weak_completion20261011
    {Samples : ℕ → Type*} [∀ index, MeasurableSpace (Samples index)]
    (laws : ∀ index, Measure (Samples index)) [∀ index, IsProbabilityMeasure (laws index)]
    (samples : ∀ index, Samples index → SkorokhodGlobalPathCompletion20261011 Space)
    (evaluations : ∀ index time, Measurable (fun outcome => samples index outcome time))
    (scales : ℕ → ℝ≥0) (scale : ℝ≥0) (convergence : Tendsto scales atTop (𝓝 scale))
    (samplesMeasurable : ∀ index, AEMeasurable
      (fun outcome => skorokhodGlobalTimeScaleCompletion20261011 (scales index) (samples index outcome)) (laws index))
    (fixedMeasurable : ∀ index, AEMeasurable
      (fun outcome => skorokhodGlobalTimeScaleCompletion20261011 scale (samples index outcome)) (laws index))
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → ℝ≥0 → Space) (continuous : ∀ outcome, Continuous (sample outcome))
    (limitEvaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (finiteMarginals : ∀ count (futureTimes : Fin count → ℝ≥0),
      Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
        ((measurable_pi_lambda _ fun coordinate => evaluations index (futureTimes coordinate)).aemeasurable)) atTop
        (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
          ((measurable_pi_lambda _ fun coordinate => limitEvaluations (futureTimes coordinate)).aemeasurable))))
    (modulus : ∀ horizon : ℝ≥0, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ index in atTop,
        ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
          ∀ outcome ∉ bad, ∀ first second : ℝ≥0, first ≤ horizon → second ≤ horizon →
            dist first second < duration → dist (samples index outcome first) (samples index outcome second) ≤ tolerance) :
    Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
      (samplesMeasurable index)) atTop
      (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
        (continuousGlobalFamily_measurable_completion20261011
          (fun outcome time => sample outcome (scale*time))
          (fun outcome => (continuous outcome).comp (continuous_const.mul continuous_id))
          (fun time => limitEvaluations (scale*time))).aemeasurable)) := by
  apply probability_ae_sample_weak_transfer_completion20261011 laws law
    (fun index outcome => skorokhodGlobalTimeScaleCompletion20261011 (scales index) (samples index outcome))
    (fun index outcome => skorokhodGlobalTimeScaleCompletion20261011 scale (samples index outcome))
    (fun outcome => (⟨fun time => sample outcome (scale*time)⟩ : SkorokhodGlobalPathCompletion20261011 Space))
    samplesMeasurable fixedMeasurable
    (continuousGlobalFamily_measurable_completion20261011
      (fun outcome time => sample outcome (scale*time))
      (fun outcome => (continuous outcome).comp (continuous_const.mul continuous_id))
      (fun time => limitEvaluations (scale*time))).aemeasurable
    (skorokhodGlobal_fixed_time_scale_weak_completion20261011 laws samples evaluations scale fixedMeasurable
      law sample continuous limitEvaluations finiteMarginals modulus)
  exact skorokhodGlobal_time_scale_coupling_probability_completion20261011 laws samples scales scale convergence modulus

end
end IGSIII34.Diffusion
