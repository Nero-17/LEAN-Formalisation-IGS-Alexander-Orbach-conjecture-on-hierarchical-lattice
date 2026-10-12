import IGSIII34.Diffusion.CountableContinuousProcessCompletion

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

/-- Continuous reconstruction is continuous along every convergent sequence
of sample-dependent times. In particular this supplies quasi-left continuity
along increasing finite stopping times, without a further regularity input. -/
theorem countableTimeContinuousSample_stopping_sequence
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (sample : ℕ → Space)
    (stoppingSequence : ℕ → ℝ≥0) (stoppingLimit : ℝ≥0)
    (convergence : Tendsto stoppingSequence atTop (𝓝 stoppingLimit)) :
    Tendsto (fun index => countableTimeContinuousSampleCompletion
      times dense sample (stoppingSequence index)) atTop
      (𝓝 (countableTimeContinuousSampleCompletion times dense sample stoppingLimit)) :=
  ((countableTimeContinuousSample_continuous_completion
    times dense sample).tendsto stoppingLimit).comp convergence

/-- The constructed continuous process has almost-sure quasi-left
continuity whenever the sample-dependent times converge almost surely.
The conclusion holds for arbitrary such times, hence also for stopping times. -/
theorem countableTimeContinuousSample_ae_stopping_sequence
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (law : ProbabilityMeasure (ℕ → Space))
    (stoppingSequence : ℕ → (ℕ → Space) → ℝ≥0)
    (stoppingLimit : (ℕ → Space) → ℝ≥0)
    (convergence : ∀ᵐ sample ∂(law : Measure (ℕ → Space)),
      Tendsto (fun index => stoppingSequence index sample) atTop (𝓝 (stoppingLimit sample))) :
    ∀ᵐ sample ∂(law : Measure (ℕ → Space)),
      Tendsto (fun index => countableTimeContinuousSampleCompletion
        times dense sample (stoppingSequence index sample)) atTop
        (𝓝 (countableTimeContinuousSampleCompletion times dense sample (stoppingLimit sample))) := by
  filter_upwards [convergence] with sample converges
  exact countableTimeContinuousSample_stopping_sequence times dense sample
    (fun index => stoppingSequence index sample) (stoppingLimit sample) converges

end
end IGSIII34.Diffusion
