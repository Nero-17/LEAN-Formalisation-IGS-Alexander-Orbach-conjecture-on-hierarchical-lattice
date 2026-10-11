import IGSIII34.Diffusion.WeightedCumulativeClockCompletion20261011
import IGSIII34.Diffusion.FinitePrefixInverseClockCompletion20261011
import IGSIII34.Diffusion.FiniteWeightedHoldingPathsCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory.Measure
open scoped BigOperators _root_.Topology

theorem weighted_inverse_clock_uniform_probability_completion20261011
    (Vertices : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, Nonempty (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    (laws : ∀ depth, ProbabilityMeasure (ℕ → Vertices depth))
    (weights : ∀ depth, Vertices depth → ℝ) (weightsPositive : ∀ depth vertex, 0 < weights depth vertex)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (divergence : Tendsto acceleration atTop atTop)
    (cumulativeClock : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => (laws depth : Measure (ℕ → Vertices depth)).prod exponentialHoldingTimeLaw
        {sample | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧ acceleration depth * tolerance <
          |weightedCumulativeClockCompletion20261011 (fun index => weights depth (sample.1 index)) sample.2 count - count|})
        atTop (𝓝 0))
    (horizon tolerance error : ℝ) (horizonNonnegative : 0 ≤ horizon)
    (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∀ᶠ depth in atTop, ∃ bad : Set ((ℕ → Vertices depth) × (ℕ → ℝ)),
      MeasurableSet bad ∧
      ((laws depth : Measure (ℕ → Vertices depth)).prod exponentialHoldingTimeLaw).real bad ≤ error ∧
      ∀ sample, sample ∉ bad → ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
        |(holdingJumpIndex (weightedHoldingSampleCompletion20261011 (weights depth) sample).2
            (acceleration depth * time) : ℝ) / acceleration depth - time| ≤ tolerance := by
  let small := min (tolerance / 2) (1 / 4)
  have smallPositive : 0 < small := lt_min (by positivity) (by norm_num)
  have smallAtMostHalf : small ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have smallAtMostTolerance : small ≤ tolerance / 2 := min_le_left _ _
  have prefixSmall := cumulativeClock (horizon + 1) small (by linarith) smallPositive
  have prefixProbability : ∀ᶠ depth in atTop,
      (laws depth : Measure (ℕ → Vertices depth)).prod exponentialHoldingTimeLaw
        {sample | ∃ count, count ≤ ⌊acceleration depth * (horizon + 1)⌋₊ ∧ acceleration depth * small <
          |weightedCumulativeClockCompletion20261011 (fun index => weights depth (sample.1 index)) sample.2 count - count|} ≤
        ENNReal.ofReal error :=
    (prefixSmall.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr errorPositive))).mono (fun _ strict => strict.le)
  have inverseSmall : ∀ᶠ depth in atTop, 1 / acceleration depth < tolerance / 2 := by
    have inverse := tendsto_inv_atTop_zero.comp divergence
    have realLimit : Tendsto (fun depth => 1 / acceleration depth) atTop (𝓝 (0 : ℝ)) := by
      simpa only [one_div, Function.comp_def] using inverse
    exact realLimit.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < tolerance / 2))
  filter_upwards [prefixProbability, inverseSmall, divergence.eventually_gt_atTop 2] with depth prefixBound inverseBound accelerationLarge
  let source := (laws depth : Measure (ℕ → Vertices depth)).prod exponentialHoldingTimeLaw
  let prefixBad := {sample : (ℕ → Vertices depth) × (ℕ → ℝ) |
    ∃ count, count ≤ ⌊acceleration depth * (horizon + 1)⌋₊ ∧ acceleration depth * small <
      |weightedCumulativeClockCompletion20261011 (fun index => weights depth (sample.1 index)) sample.2 count - count|}
  have prefixMeasurable : MeasurableSet prefixBad := by
    simp only [prefixBad, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro count
    by_cases permitted : count ≤ ⌊acceleration depth * (horizon + 1)⌋₊
    · simp only [permitted, true_and]
      apply measurableSet_lt measurable_const
      apply continuous_abs.measurable.comp
      apply Measurable.sub _ measurable_const
      unfold weightedCumulativeClockCompletion20261011
      apply Finset.measurable_sum
      intro index _
      exact ((measurable_of_finite (weights depth)).comp ((measurable_pi_apply index).comp measurable_fst)).mul
        ((measurable_pi_apply index).comp measurable_snd)
    · simp only [permitted, false_and, Set.setOf_false, MeasurableSet.empty]
  have originalRegular : ∀ᵐ sample ∂source, (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop := by
    have positive := (quasiMeasurePreserving_snd (μ := (laws depth : Measure (ℕ → Vertices depth)))
      (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_positive
    have nonexplosion := (quasiMeasurePreserving_snd (μ := (laws depth : Measure (ℕ → Vertices depth)))
      (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_nonexplosion
    exact positive.and nonexplosion
  have regular := weightedHoldingSample_regular_completion20261011 source (weights depth) (weightsPositive depth) originalRegular
  let clockBad := toMeasurable source {sample | ¬ ((∀ index, 0 < (weightedHoldingSampleCompletion20261011 (weights depth) sample).2 index) ∧
    Tendsto (cumulativeHoldingTime (weightedHoldingSampleCompletion20261011 (weights depth) sample).2) atTop atTop)}
  have clockNull : source clockBad = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp regular
  refine ⟨prefixBad ∪ clockBad, prefixMeasurable.union (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · have estimate : source (prefixBad ∪ clockBad) ≤ ENNReal.ofReal error :=
      (measure_union_le _ _).trans (by simpa only [clockNull, add_zero] using prefixBound)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top estimate).trans_eq (ENNReal.toReal_ofReal errorPositive.le)
  · intro sample outside time timeNonnegative timeBound
    have outsidePrefix : sample ∉ prefixBad := fun member => outside (Or.inl member)
    have outsideClock : sample ∉ clockBad := fun member => outside (Or.inr member)
    have clock : (∀ index, 0 < (weightedHoldingSampleCompletion20261011 (weights depth) sample).2 index) ∧
        Tendsto (cumulativeHoldingTime (weightedHoldingSampleCompletion20261011 (weights depth) sample).2) atTop atTop := by
      by_contra failure
      exact outsideClock (subset_toMeasurable source _ failure)
    have good (count : ℕ) (countBound : count ≤ ⌊acceleration depth * (horizon + 1)⌋₊) :
        |cumulativeHoldingTime (weightedHoldingSampleCompletion20261011 (weights depth) sample).2 count - count| ≤
          acceleration depth * small := by
      apply le_of_not_gt
      intro failure
      exact outsidePrefix ⟨count, countBound, failure⟩
    have estimate := holdingJumpIndex_uniform_of_finite_prefix_completion20261011
      (weightedHoldingSampleCompletion20261011 (weights depth) sample).2 clock.1 clock.2
      (acceleration depth) horizon small accelerationLarge horizonNonnegative smallPositive.le smallAtMostHalf
      good time timeNonnegative timeBound
    exact estimate.trans (by linarith)

end
end IGSIII34.Diffusion
