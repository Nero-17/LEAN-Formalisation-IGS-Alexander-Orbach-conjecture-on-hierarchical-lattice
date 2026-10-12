import IGSIII34.Diffusion.WeightedExponentialNoiseUniformCompletion

set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators _root_.Topology

def weightedCumulativeClockCompletion (weights holding : ℕ → ℝ) (count : ℕ) : ℝ :=
  ∑ index ∈ Finset.range count, weights index * holding index

def centeredWeightClockCompletion (weights : ℕ → ℝ) (count : ℕ) : ℝ :=
  ∑ index ∈ Finset.range count, (weights index - 1)

theorem weightedCumulativeClock_decomposition_completion (weights holding : ℕ → ℝ) (count : ℕ) :
    weightedCumulativeClockCompletion weights holding count - count =
      weightedExponentialNoiseCompletion weights count holding + centeredWeightClockCompletion weights count := by
  simp only [weightedCumulativeClockCompletion, weightedExponentialNoiseCompletion,
    centeredWeightClockCompletion, mul_sub, mul_one, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- Real weighted cumulative clocks converge uniformly on every bounded
jump-index interval once the true chain's centered additive clock does.
Independent exponential noise is proved small inside this theorem. -/
theorem weightedCumulativeClock_uniform_probability_completion
    (Outcomes : ℕ → Type*) [∀ depth, MeasurableSpace (Outcomes depth)]
    (laws : ∀ depth, Measure (Outcomes depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (weights : ∀ depth, Outcomes depth → ℕ → ℝ)
    (weightsMeasurable : ∀ depth index, Measurable (fun outcome => weights depth outcome index))
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (weightsNonnegative : ∀ depth outcome index, 0 ≤ weights depth outcome index)
    (weightsBounded : ∀ depth outcome index, weights depth outcome index ≤ bound)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (divergence : Tendsto acceleration atTop atTop)
    (meanClock : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => laws depth {outcome | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧
        acceleration depth * tolerance < |centeredWeightClockCompletion (weights depth outcome) count|}) atTop (𝓝 0))
    (horizon tolerance : ℝ) (horizonNonnegative : 0 ≤ horizon) (tolerancePositive : 0 < tolerance) :
    Tendsto (fun depth => (laws depth).prod exponentialHoldingTimeLaw
      {sample | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧ acceleration depth * tolerance <
        |weightedCumulativeClockCompletion (weights depth sample.1) sample.2 count - count|}) atTop (𝓝 0) := by
  have noiseSmall := weightedExponentialNoise_uniform_probability_completion Outcomes laws weights weightsMeasurable
    bound boundNonnegative weightsNonnegative weightsBounded acceleration accelerationPositive divergence horizon
    (tolerance / 2) horizonNonnegative (by positivity)
  have meanSmall := meanClock horizon (tolerance / 2) horizonNonnegative (by positivity)
  have sumSmall := noiseSmall.add meanSmall
  simp only [zero_add] at sumSmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sumSmall (fun _ => bot_le)
  intro depth
  let noiseBad := {sample : Outcomes depth × (ℕ → ℝ) | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧
    acceleration depth * (tolerance / 2) < |weightedExponentialNoiseCompletion (weights depth sample.1) count sample.2|}
  let meanBad := {outcome : Outcomes depth | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧
    acceleration depth * (tolerance / 2) < |centeredWeightClockCompletion (weights depth outcome) count|}
  have subset : {sample : Outcomes depth × (ℕ → ℝ) | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧
      acceleration depth * tolerance < |weightedCumulativeClockCompletion (weights depth sample.1) sample.2 count - count|} ⊆
      noiseBad ∪ meanBad ×ˢ Set.univ := by
    intro sample failure
    obtain ⟨count, countBound, failure⟩ := failure
    by_cases largeNoise : acceleration depth * (tolerance / 2) <
        |weightedExponentialNoiseCompletion (weights depth sample.1) count sample.2|
    · exact Or.inl ⟨count, countBound, largeNoise⟩
    apply Or.inr
    refine ⟨⟨count, countBound, ?_⟩, Set.mem_univ _⟩
    rw [weightedCumulativeClock_decomposition_completion] at failure
    have triangle := abs_add_le (weightedExponentialNoiseCompletion (weights depth sample.1) count sample.2)
      (centeredWeightClockCompletion (weights depth sample.1) count)
    linarith [le_of_not_gt largeNoise]
  calc
    _ ≤ (laws depth).prod exponentialHoldingTimeLaw (noiseBad ∪ meanBad ×ˢ Set.univ) := measure_mono subset
    _ ≤ (laws depth).prod exponentialHoldingTimeLaw noiseBad +
        (laws depth).prod exponentialHoldingTimeLaw (meanBad ×ˢ Set.univ) := measure_union_le _ _
    _ = _ := by rw [Measure.prod_prod, measure_univ]; simp [noiseBad, meanBad]

end
end IGSIII34.Diffusion
