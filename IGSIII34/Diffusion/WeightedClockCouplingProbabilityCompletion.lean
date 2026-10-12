import IGSIII34.Diffusion.WeightedInverseClockProbabilityCompletion
import IGSIII34.Diffusion.CTDiscreteClockCouplingCompletion

set_option autoImplicit false
set_option maxHeartbeats 3800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators _root_.Topology

/-- The actual state-dependent exponential clock is compared to the same
neighbour chain's floor clock. All weighted exponential noise is discharged. -/
theorem weightedClock_uniform_coupling_probability_completion
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (Vertices : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, Nonempty (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    (laws : ∀ depth, ProbabilityMeasure (ℕ → Vertices depth))
    (placement : ∀ depth, Vertices depth → Space)
    (weights : ∀ depth, Vertices depth → ℝ) (weightsPositive : ∀ depth vertex, 0 < weights depth vertex)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (weightsBounded : ∀ depth vertex, weights depth vertex ≤ bound)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop)
    (centeredClock : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => (laws depth : Measure (ℕ → Vertices depth))
        {trajectory | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧ acceleration depth * tolerance <
          |centeredWeightClockCompletion (fun index => weights depth (trajectory index)) count|}) atTop (𝓝 0))
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (laws depth : Measure (ℕ → Vertices depth)).real (finiteIntervalChainBadModulusCompletion
          (placement depth) (acceleration depth) horizon duration tolerance) ≤ error)
    (horizon : ℕ) (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∀ᶠ depth in atTop, ∃ bad : Set ((ℕ → Vertices depth) × (ℕ → ℝ)),
      MeasurableSet bad ∧ ((laws depth : Measure (ℕ → Vertices depth)).prod exponentialHoldingTimeLaw).real bad ≤ error ∧
      ∀ outcome ∉ bad, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
        dist (placement depth (holdingTimePath outcome.1
          (weightedHoldingSampleCompletion (weights depth) outcome).2 (acceleration depth * time)))
          (placement depth (outcome.1 ⌊acceleration depth * time⌋₊)) ≤ tolerance := by
  have cumulativeClock := weightedCumulativeClock_uniform_probability_completion
    (fun depth => ℕ → Vertices depth) (fun depth => (laws depth : Measure (ℕ → Vertices depth)))
    (fun depth trajectory index => weights depth (trajectory index))
    (fun depth index => (measurable_of_finite (weights depth)).comp (measurable_pi_apply index))
    bound boundNonnegative (fun depth trajectory index => (weightsPositive depth (trajectory index)).le)
    (fun depth trajectory index => weightsBounded depth (trajectory index))
    acceleration accelerationPositive diverge centeredClock
  obtain ⟨duration, durationPositive, chainProbabilities⟩ := chainModulus (horizon + 1) tolerance (error / 2)
    tolerancePositive (by positivity)
  let clockTolerance := min duration 1 / 2
  have clockPositive : 0 < clockTolerance := by dsimp [clockTolerance]; positivity
  have clockWithinDuration : clockTolerance ≤ duration := by
    have minimum := min_le_left duration (1 : ℝ)
    dsimp only [clockTolerance]
    linarith
  have clockWithinOne : clockTolerance ≤ 1 := by
    have minimum := min_le_right duration (1 : ℝ)
    dsimp only [clockTolerance]
    linarith
  have clockProbabilities := weighted_inverse_clock_uniform_probability_completion Vertices laws weights weightsPositive
    acceleration accelerationPositive diverge cumulativeClock horizon clockTolerance (error / 2)
    (Nat.cast_nonneg horizon) clockPositive (by positivity)
  filter_upwards [chainProbabilities, clockProbabilities] with depth chainProbability clockProbability
  obtain ⟨clockBad, clockMeasurable, clockProbability, clockGood⟩ := clockProbability
  let chainBad := finiteIntervalChainBadModulusCompletion (placement depth) (acceleration depth) (horizon + 1 : ℕ) duration tolerance
  have chainMeasurable : MeasurableSet chainBad := finiteIntervalChainBadModulus_measurable_completion
    (placement depth) (measurable_of_finite _) _ _ _ _
  refine ⟨chainBad ×ˢ Set.univ ∪ clockBad, (chainMeasurable.prod MeasurableSet.univ).union clockMeasurable, ?_, ?_⟩
  · have probability := measureReal_union_le (μ := (laws depth : Measure (ℕ → Vertices depth)).prod exponentialHoldingTimeLaw)
      (chainBad ×ˢ (Set.univ : Set (ℕ → ℝ))) clockBad
    simp only [measureReal_prod_prod, probReal_univ, mul_one] at probability
    exact probability.trans (by linarith)
  · intro outcome outside time timeNonnegative timeBound
    have outsideChain : outcome.1 ∉ chainBad := fun failure => outside (Or.inl ⟨failure, Set.mem_univ _⟩)
    have outsideClock : outcome ∉ clockBad := fun failure => outside (Or.inr failure)
    exact finiteChain_good_clock_coupling_completion (placement depth) outcome.1
      (weightedHoldingSampleCompletion (weights depth) outcome).2
      (acceleration depth) (accelerationPositive depth) horizon duration clockTolerance tolerance
      clockWithinDuration clockWithinOne outsideChain (clockGood outcome outsideClock)
      time timeNonnegative timeBound

end
end IGSIII34.Diffusion
