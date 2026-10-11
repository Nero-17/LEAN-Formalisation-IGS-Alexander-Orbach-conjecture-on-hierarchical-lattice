import IGSIII34.Diffusion.GreedyClockRoundingCompletion20261011
import IGSIII34.Diffusion.CompactPlateauCoverCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Vertex Edge Label Space : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [StandardBorelSpace Vertex]
  [Nonempty Vertex] [Fintype Edge] [Fintype Label]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem finiteGraphResolvent_observed_two_cover_modulus_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (times : ℕ → ℝ≥0) (embedding : Vertex → Space) (embeddingMeasurable : Measurable embedding)
    (centers : Label → Space) (radius : ℝ) (radiusPositive : 0 < radius)
    (cover : ∀ point, ∃ label, compactPlateauCompletion20261011 (centers label) radius point = 1)
    (acceleration : ℝ) (accelerationPositive : 0 < acceleration)
    (largeParameter smallParameter : ℝ) (largeParameterPositive : 0 < largeParameter) (smallParameterPositive : 0 < smallParameter)
    (largeError smallError : ℝ) (largeErrorNonnegative : 0 ≤ largeError) (smallErrorNonnegative : 0 ≤ smallError)
    (largeErrorBelowHalf : largeError < 1 / 2) (smallErrorBelowHalf : smallError < 1 / 2)
    (largeApproximation : ∀ label vertex,
      |finiteGraphResolvent endpoint positiveDegree largeParameter acceleration largeParameterPositive accelerationPositive.le
        (fun point => largeParameter * compactPlateauCompletion20261011 (centers label) radius (embedding point)) vertex -
          compactPlateauCompletion20261011 (centers label) radius (embedding vertex)| ≤ largeError)
    (smallApproximation : ∀ label vertex,
      |finiteGraphResolvent endpoint positiveDegree smallParameter acceleration smallParameterPositive accelerationPositive.le
        (fun point => smallParameter * compactPlateauCompletion20261011 (centers label) radius (embedding point)) vertex -
          compactPlateauCompletion20261011 (centers label) radius (embedding vertex)| ≤ smallError)
    (horizon steps : ℕ) (largeDuration smallDuration : ℝ)
    (largeDurationPositive : 0 < largeDuration) (smallDurationPositive : 0 < smallDuration)
    (stepsPositive : 0 < steps) (largeGap : 4 * (horizon : ℝ) + 1 < steps * largeDuration)
    (clockLarge : 2 * (steps : ℝ) ≤ acceleration) (clockSmall : 4 ≤ acceleration * smallDuration)
    (jump tolerance : ℝ) (jumpNonnegative : 0 ≤ jump) (toleranceLarge : 3 * radius + jump ≤ tolerance)
    (jumpBound : ∀ᵐ path ∂finiteDiscreteWalkLaw endpoint positiveDegree initial,
      ∀ index, dist (embedding (path index)) (embedding (path (index + 1))) ≤ jump) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial |>.map
      (flooredCountableObservationCompletion20261011 times embedding acceleration)).real
      (countableTimeBadModulusCompletion20261011 times horizon (smallDuration / 2) tolerance) ≤
      2 * (2 * Fintype.card Label * (largeError + 2 * largeParameter * largeDuration)) +
        steps * (2 * Fintype.card Label * (smallError + 2 * smallParameter * smallDuration)) := by
  let largeForcing := fun label vertex => largeParameter * compactPlateauCompletion20261011 (centers label) radius (embedding vertex)
  let smallForcing := fun label vertex => smallParameter * compactPlateauCompletion20261011 (centers label) radius (embedding vertex)
  have forcingBound (parameter : ℝ) (parameterPositive : 0 < parameter) (label : Label) (vertex : Vertex) :
      |parameter * compactPlateauCompletion20261011 (centers label) radius (embedding vertex)| ≤ parameter := by
    rw [abs_mul, abs_of_pos parameterPositive,
      abs_of_nonneg (compactPlateau_unit_interval_completion20261011 _ _ _).1]
    exact mul_le_of_le_one_right parameterPositive.le (compactPlateau_unit_interval_completion20261011 _ _ _).2
  have largeCover := compactPlateau_approximation_cover_completion20261011 centers embedding radius radiusPositive
    largeError largeErrorNonnegative largeErrorBelowHalf cover _ largeApproximation
  have smallCover := compactPlateau_approximation_cover_completion20261011 centers embedding radius radiusPositive
    smallError smallErrorNonnegative smallErrorBelowHalf cover _ smallApproximation
  have rounded := greedy_clock_rounding_completion20261011 acceleration horizon largeDuration smallDuration steps
    accelerationPositive (Nat.cast_nonneg _) largeDurationPositive smallDurationPositive stepsPositive largeGap clockLarge clockSmall
  have halfGap := rounded.2.2
  have denominator : (⌊acceleration * (horizon : ℝ)⌋₊ : ℝ) < steps * ⌊acceleration * largeDuration⌋₊ := by
    have : (0 : ℝ) ≤ ⌊acceleration * (horizon : ℝ)⌋₊ := Nat.cast_nonneg _
    linarith
  have discrete := finiteGraphResolvent_two_cover_clock_modulus_completion20261011
    endpoint positiveDegree initial embedding acceleration accelerationPositive largeParameter smallParameter
    largeParameterPositive smallParameterPositive largeForcing smallForcing
    (forcingBound largeParameter largeParameterPositive) (forcingBound smallParameter smallParameterPositive)
    radius radiusPositive largeError smallError (1 / 2) (1 / 2) largeErrorNonnegative smallErrorNonnegative
    (by norm_num) (by norm_num) largeCover.1 smallCover.1
    (fun label first last initial far => (largeCover.2 label first last initial far).trans largeErrorBelowHalf.le)
    (fun label first last initial far => (smallCover.2 label first last initial far).trans smallErrorBelowHalf.le)
    steps ⌊acceleration * (horizon : ℝ)⌋₊ ⌊acceleration * largeDuration⌋₊ ⌈acceleration * (smallDuration / 2) + 1⌉₊
    denominator largeDuration smallDuration rounded.1 rounded.2.1 jump jumpNonnegative
    (jumpBound.mono (fun path bound index _ => bound index))
  have observation := flooredCountableObservation_bad_modulus_probability_completion20261011
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) times embedding embeddingMeasurable acceleration accelerationPositive.le
    horizon (smallDuration / 2) tolerance
  refine observation.trans (le_trans ?_ (discrete.trans ?_))
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    rintro path ⟨first, last, ordered, within, gap, far⟩
    exact ⟨first, last, ordered, within, gap, toleranceLarge.trans_lt far⟩
  · have factor := greedy_clock_exit_factor_completion20261011
      ⌊acceleration * (horizon : ℝ)⌋₊ ⌊acceleration * largeDuration⌋₊ steps halfGap
      ((Fintype.card Label * (largeError + 2 * largeParameter * largeDuration)) / (1 - (1 / 2))) (by positivity)
    have total := add_le_add_right factor
      ((steps : ℝ) * ((Fintype.card Label * (smallError + 2 * smallParameter * smallDuration)) / (1 - (1 / 2))))
    norm_num at total ⊢
    nlinarith

end
end IGSIII34.Diffusion
