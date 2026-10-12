import IGSIII34.Diffusion.DenseObservationFiniteTimesCompletion
import IGSIII34.Diffusion.CountableWeakFiniteMarginalsCompletion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def countableReobservedContinuousSampleCompletion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (futureTimes : ℕ → ℝ≥0)
    (path : ℕ → Space) : ℕ → Space :=
  fun index => countableTimeContinuousSampleCompletion times dense path (futureTimes index)

theorem countableReobservedContinuousSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (futureTimes : ℕ → ℝ≥0) :
    Measurable (countableReobservedContinuousSampleCompletion (Space := Space) times dense futureTimes) :=
  measurable_pi_lambda _ fun index =>
    countableTimeContinuousSample_evaluation_measurable_completion times dense (futureTimes index)

/-- Dense observation weak convergence and actual all-index modulus
bounds identify the entire countable observation law for every new
enumeration of real times. -/
theorem denseObservedWalk_reobserve_weak_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth)) (scales : ℕ → ℝ) (scaleNonnegative : ∀ depth, 0 ≤ scales depth)
    (placement : ∀ depth, Vertices depth → Space)
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (limitLaw : ProbabilityMeasure (ℕ → Space))
    (weak : Tendsto (fun depth => discreteRescaledObservationLawCompletion (endpoint depth) (positiveDegree depth)
      (initial depth) (scales depth) times (placement depth)) atTop (𝓝 limitLaw))
    (regular : ∀ᵐ path ∂(limitLaw : Measure (ℕ → Space)), countableTimeLocalUniformContinuityCompletion times path)
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion (placement depth) (scales depth) horizon duration tolerance) ≤ error)
    (futureTimes : ℕ → ℝ≥0) :
    Tendsto (fun depth => discreteRescaledObservationLawCompletion (endpoint depth) (positiveDegree depth)
      (initial depth) (scales depth) futureTimes (placement depth)) atTop
      (𝓝 (limitLaw.map (countableReobservedContinuousSample_measurable_completion times dense futureTimes).aemeasurable)) := by
  apply countableTimeLaws_weak_of_finite_marginals_completion
  intro count coordinates
  obtain ⟨bound, bounded⟩ := (Set.finite_range (fun index : Fin count => (futureTimes (coordinates index) : ℝ) + 1)).bddAbove
  obtain ⟨horizon, large⟩ := exists_nat_ge bound
  have within (index : Fin count) : (futureTimes (coordinates index) : ℝ) + 1 ≤ horizon :=
    (bounded (Set.mem_range_self index)).trans large
  have marginal := finiteFlooredTimeLaw_weak_of_dense_observations_completion
    Vertices Edges endpoint positiveDegree initial scales scaleNonnegative placement times dense limitLaw weak regular
    (fun index => futureTimes (coordinates index)) horizon within (chainModulus horizon)
  convert marginal using 1
  · funext depth
    apply Subtype.ext
    change ((finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).map
        (discreteRescaledObservationCompletion (scales depth) futureTimes (placement depth))).map
        (fun path : ℕ → Space => fun index : Fin count => path (coordinates index)) =
      (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).map
        (finiteFlooredTimeSampleCompletion (scales depth) (fun index => futureTimes (coordinates index)) (placement depth))
    rw [Measure.map_map (by fun_prop : Measurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates index)))
      (discreteRescaledObservation_measurable_completion _ _ _)]
    rfl
  · apply congrArg (fun probability : ProbabilityMeasure (Fin count → Space) => 𝓝 probability)
    apply Subtype.ext
    change ((limitLaw : Measure (ℕ → Space)).map
        (countableReobservedContinuousSampleCompletion times dense futureTimes)).map
        (fun path : ℕ → Space => fun index : Fin count => path (coordinates index)) =
      (limitLaw : Measure (ℕ → Space)).map
        (fun path : ℕ → Space => fun index : Fin count => countableTimeContinuousSampleCompletion times dense path (futureTimes (coordinates index)))
    rw [Measure.map_map (by fun_prop : Measurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates index)))
      (countableReobservedContinuousSample_measurable_completion _ _ _)]
    rfl

end
end IGSIII34.Diffusion
