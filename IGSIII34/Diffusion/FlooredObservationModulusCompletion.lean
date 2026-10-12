import IGSIII34.Diffusion.CountablePathContinuityCompletion
import IGSIII34.Diffusion.FiniteResolventGreedyClockCompletion
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

variable {Vertex Space : Type*} [MeasurableSpace Vertex]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

def flooredCountableObservationCompletion (times : ℕ → ℝ≥0)
    (embedding : Vertex → Space) (acceleration : ℝ) (path : ℕ → Vertex) : ℕ → Space :=
  fun coordinate => embedding (path ⌊acceleration * (times coordinate : ℝ)⌋₊)

theorem flooredCountableObservation_measurable_completion
    (times : ℕ → ℝ≥0) (embedding : Vertex → Space) (embeddingMeasurable : Measurable embedding)
    (acceleration : ℝ) : Measurable (flooredCountableObservationCompletion times embedding acceleration) := by
  apply measurable_pi_lambda
  intro coordinate
  exact embeddingMeasurable.comp (measurable_pi_apply _)

theorem floor_observation_gap_completion
    (acceleration duration : ℝ) (accelerationNonnegative : 0 ≤ acceleration)
    (first last : ℝ≥0) (close : dist first last < duration) :
    ⌊acceleration * (last : ℝ)⌋₊ ≤ ⌊acceleration * (first : ℝ)⌋₊ + ⌈acceleration * duration + 1⌉₊ := by
  have firstLower := Nat.lt_floor_add_one (acceleration * (first : ℝ))
  have lastUpper := Nat.floor_le (show 0 ≤ acceleration * (last : ℝ) by positivity)
  have ceilLower := Nat.le_ceil (acceleration * duration + 1)
  have delta : (last : ℝ) - first < duration := by
    have absolute : |(first : ℝ) - last| < duration := close
    linarith [(abs_lt.mp absolute).1]
  have multiplied := mul_le_mul_of_nonneg_left delta.le accelerationNonnegative
  have realBound : (⌊acceleration * (last : ℝ)⌋₊ : ℝ) ≤
      (⌊acceleration * (first : ℝ)⌋₊ + ⌈acceleration * duration + 1⌉₊ : ℕ) := by
    simp only [Nat.cast_add]
    nlinarith
  exact_mod_cast realBound

theorem flooredCountableObservation_bad_modulus_subset_completion
    (times : ℕ → ℝ≥0) (embedding : Vertex → Space) (acceleration : ℝ)
    (accelerationNonnegative : 0 ≤ acceleration) (horizon : ℕ) (duration tolerance : ℝ) :
    flooredCountableObservationCompletion times embedding acceleration ⁻¹'
      countableTimeBadModulusCompletion times horizon duration tolerance ⊆
      {path | ∃ first last, first ≤ last ∧ last ≤ ⌊acceleration * (horizon : ℝ)⌋₊ ∧
        last ≤ first + ⌈acceleration * duration + 1⌉₊ ∧ tolerance < dist (embedding (path first)) (embedding (path last))} := by
  rintro path ⟨first, last, firstBound, lastBound, close, far⟩
  have firstIndexBound := Nat.floor_mono (mul_le_mul_of_nonneg_left firstBound accelerationNonnegative)
  have lastIndexBound := Nat.floor_mono (mul_le_mul_of_nonneg_left lastBound accelerationNonnegative)
  rcases le_total ⌊acceleration * (times first : ℝ)⌋₊ ⌊acceleration * (times last : ℝ)⌋₊ with ordered | ordered
  · exact ⟨_, _, ordered, lastIndexBound,
      floor_observation_gap_completion acceleration duration accelerationNonnegative _ _ close, far⟩
  · refine ⟨_, _, ordered, firstIndexBound,
      floor_observation_gap_completion acceleration duration accelerationNonnegative _ _ ?_, ?_⟩
    · simpa only [dist_comm] using close
    · simpa only [flooredCountableObservationCompletion, dist_comm] using far

theorem flooredCountableObservation_bad_modulus_probability_completion
    (law : Measure (ℕ → Vertex)) [IsProbabilityMeasure law]
    (times : ℕ → ℝ≥0) (embedding : Vertex → Space) (embeddingMeasurable : Measurable embedding)
    (acceleration : ℝ) (accelerationNonnegative : 0 ≤ acceleration) (horizon : ℕ) (duration tolerance : ℝ) :
    (law.map (flooredCountableObservationCompletion times embedding acceleration)).real
      (countableTimeBadModulusCompletion times horizon duration tolerance) ≤
      law.real {path | ∃ first last, first ≤ last ∧ last ≤ ⌊acceleration * (horizon : ℝ)⌋₊ ∧
        last ≤ first + ⌈acceleration * duration + 1⌉₊ ∧ tolerance < dist (embedding (path first)) (embedding (path last))} := by
  rw [Measure.real_def, Measure.map_apply
    (flooredCountableObservation_measurable_completion times embedding embeddingMeasurable acceleration)
    (countableTimeBadModulus_isOpen_completion times horizon duration tolerance).measurableSet]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (flooredCountableObservation_bad_modulus_subset_completion
      times embedding acceleration accelerationNonnegative horizon duration tolerance))

end
end IGSIII34.Diffusion
