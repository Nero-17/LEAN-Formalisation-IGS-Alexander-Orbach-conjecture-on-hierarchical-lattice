import IGSIII34.Diffusion.CountablePathMeasurableExtensionCompletion

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def countableContinuousProcessProbabilityLawCompletion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (law : ProbabilityMeasure (ℕ → Space)) :
    ProbabilityMeasure (ℝ≥0 → Space) :=
  law.map (countableTimeContinuousSample_measurable_completion times dense).aemeasurable

theorem countableContinuousProcess_observed_marginal_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (law : ProbabilityMeasure (ℕ → Space))
    (regular : ∀ᵐ path ∂(law : Measure (ℕ → Space)), countableTimeLocalUniformContinuityCompletion times path)
    (coordinate : ℕ) :
    (countableContinuousProcessProbabilityLawCompletion times dense law : Measure (ℝ≥0 → Space)).map
      (fun path => path (times coordinate)) = (law : Measure (ℕ → Space)).map (fun path => path coordinate) := by
  change ((law : Measure (ℕ → Space)).map (countableTimeContinuousSampleCompletion times dense)).map _ = _
  rw [Measure.map_map (measurable_pi_apply (times coordinate))
    (countableTimeContinuousSample_measurable_completion times dense)]
  apply Measure.map_congr
  filter_upwards [countableTimeContinuousSample_ae_agreement_completion times dense law regular] with path agrees
  exact agrees coordinate

theorem countableContinuousProcess_observed_finite_marginal_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (law : ProbabilityMeasure (ℕ → Space))
    (regular : ∀ᵐ path ∂(law : Measure (ℕ → Space)), countableTimeLocalUniformContinuityCompletion times path)
    {count : ℕ} (coordinates : Fin count → ℕ) :
    (countableContinuousProcessProbabilityLawCompletion times dense law : Measure (ℝ≥0 → Space)).map
      (fun path => fun index : Fin count => path (times (coordinates index))) =
        (law : Measure (ℕ → Space)).map (fun path => fun index : Fin count => path (coordinates index)) := by
  change ((law : Measure (ℕ → Space)).map (countableTimeContinuousSampleCompletion times dense)).map _ = _
  rw [Measure.map_map (by fun_prop : Measurable (fun path : ℝ≥0 → Space => fun index : Fin count => path (times (coordinates index))))
    (countableTimeContinuousSample_measurable_completion times dense)]
  apply Measure.map_congr
  filter_upwards [countableTimeContinuousSample_ae_agreement_completion times dense law regular] with path agrees
  funext index
  exact agrees (coordinates index)

/-- A countable weak limit with the proved modulus probability estimates
constructs a measurable continuous process on its original probability
space and preserves every observed finite-dimensional distribution. -/
theorem countableTimeWeakLimit_continuous_process_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (laws : ℕ → ProbabilityMeasure (ℕ → Space))
    (limitLaw : ProbabilityMeasure (ℕ → Space)) (convergence : Tendsto laws atTop (𝓝 limitLaw))
    (bounds : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop, (laws depth : Measure (ℕ → Space)).real
        (countableTimeBadModulusCompletion times horizon duration tolerance) ≤ error) :
    Measurable (countableTimeContinuousSampleCompletion (Space := Space) times dense) ∧
      (∀ sample : ℕ → Space, Continuous (countableTimeContinuousSampleCompletion times dense sample)) ∧
      (∀ᵐ sample ∂(limitLaw : Measure (ℕ → Space)), ∀ coordinate,
        countableTimeContinuousSampleCompletion times dense sample (times coordinate) = sample coordinate) ∧
      (∀ (count : ℕ) (coordinates : Fin count → ℕ),
        (countableContinuousProcessProbabilityLawCompletion times dense limitLaw : Measure (ℝ≥0 → Space)).map
          (fun path => fun index : Fin count => path (times (coordinates index))) =
            (limitLaw : Measure (ℕ → Space)).map (fun path => fun index : Fin count => path (coordinates index))) := by
  have regular := countableTimeWeakLimit_ae_local_uniform_continuity_completion times laws limitLaw convergence bounds
  refine ⟨countableTimeContinuousSample_measurable_completion times dense,
    countableTimeContinuousSample_continuous_completion times dense,
    countableTimeContinuousSample_ae_agreement_completion times dense limitLaw regular, ?_⟩
  intro count coordinates
  exact countableContinuousProcess_observed_finite_marginal_completion times dense limitLaw regular coordinates

end
end IGSIII34.Diffusion
