import IGSIII34.Diffusion.FiniteResolventChainModulusCompletion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Space Label : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [Fintype Label] [Nonempty Label]
  (Vertex Edge : ℕ → Type*) [∀ depth, Fintype (Vertex depth)] [∀ depth, DecidableEq (Vertex depth)]
  [∀ depth, MeasurableSpace (Vertex depth)] [∀ depth, MeasurableSingletonClass (Vertex depth)]
  [∀ depth, StandardBorelSpace (Vertex depth)] [∀ depth, Nonempty (Vertex depth)]
  [∀ depth, Fintype (Edge depth)]

/-- Vanishing actual edge jumps and approximation of fixed continuous
plateaux by true finite graph resolvents imply tight countable-time
moduli. The approximation premise is an analytic resolvent premise,
not a path-continuity or tightness premise. -/
theorem finite_resolvent_chain_tightness_completion
    (endpoint : ∀ depth, Edge depth → Vertex depth × Vertex depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertex depth))
    (embedding : ∀ depth, Vertex depth → Space)
    (embeddingMeasurable : ∀ depth, Measurable (embedding depth))
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (accelerationDiverges : Tendsto acceleration atTop atTop)
    (centers : Label → Space) (radius : ℝ) (radiusPositive : 0 < radius)
    (cover : ∀ point, ∃ label, compactPlateauCompletion (centers label) radius point = 1)
    (resolventApproximation : ∀ error : ℝ, 0 < error → ∃ parameter : ℝ, ∃ parameterPositive : 0 < parameter,
      1 ≤ parameter ∧ ∀ᶠ depth in atTop, ∀ label vertex,
        |finiteGraphResolvent (endpoint depth) (positiveDegree depth) parameter (acceleration depth) parameterPositive
          (accelerationPositive depth).le
          (fun point => parameter * compactPlateauCompletion (centers label) radius (embedding depth point)) vertex -
            compactPlateauCompletion (centers label) radius (embedding depth vertex)| ≤ error)
    (jumpBound : ∀ᶠ depth in atTop, ∀ᵐ path ∂finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth),
      ∀ index, dist (embedding depth (path index)) (embedding depth (path (index + 1))) ≤ radius)
    (horizon : ℕ) (probability : ℝ) (probabilityPositive : 0 < probability) :
    ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
      (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
        {path | ∃ first last, first ≤ last ∧ last ≤ ⌊acceleration depth * (horizon : ℝ)⌋₊ ∧
          last ≤ first + ⌈acceleration depth * duration + 1⌉₊ ∧
          4 * radius < dist (embedding depth (path first)) (embedding depth (path last))} ≤ probability := by
  have choices : ∀ error : ℝ, ∃ parameter : ℝ, ∃ parameterPositive : 0 < parameter,
      1 ≤ parameter ∧ (0 < error → ∀ᶠ depth in atTop, ∀ label vertex,
        |finiteGraphResolvent (endpoint depth) (positiveDegree depth) parameter (acceleration depth) parameterPositive
          (accelerationPositive depth).le
          (fun point => parameter * compactPlateauCompletion (centers label) radius (embedding depth point)) vertex -
            compactPlateauCompletion (centers label) radius (embedding depth vertex)| ≤ min error (1 / 4)) := by
    intro error
    by_cases positive : 0 < error
    · obtain ⟨parameter, parameterPositive, parameterOne, approximation⟩ := resolventApproximation
        (min error (1 / 4)) (by positivity)
      exact ⟨parameter, parameterPositive, parameterOne, fun _ => approximation⟩
    · exact ⟨1, by norm_num, le_rfl, fun contrary => False.elim (positive contrary)⟩
  choose parameter parameterPositive parameterOne approximation using choices
  have labelsPositive : (0 : ℝ) < Fintype.card Label := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨largeError, largeDuration, steps, smallError, smallDuration,
    largeErrorPositive, largeDurationPositive, stepsPositive, smallErrorPositive, smallDurationPositive, largeGap, total⟩ :=
    exists_two_cover_modulus_parameters_completion (Fintype.card Label) horizon probability labelsPositive
      (Nat.cast_nonneg _) probabilityPositive parameter (fun error _ => parameterPositive error)
  refine ⟨smallDuration / 2, by positivity, ?_⟩
  have largeApproximation := approximation largeError largeErrorPositive
  have smallApproximation := approximation smallError smallErrorPositive
  have clocksLarge := accelerationDiverges.eventually (eventually_ge_atTop (2 * (steps : ℝ)))
  have clocksSmall := accelerationDiverges.eventually (eventually_ge_atTop (4 / smallDuration))
  filter_upwards [largeApproximation, smallApproximation, clocksLarge, clocksSmall, jumpBound]
    with depth largeApproximation smallApproximation clockLarge clockSmall jumpBound
  have observed := finiteGraphResolvent_chain_two_cover_modulus_completion
    (endpoint depth) (positiveDegree depth) (initial depth) (embedding depth) (embeddingMeasurable depth)
    centers radius radiusPositive cover (acceleration depth) (accelerationPositive depth)
    (parameter largeError) (parameter smallError) (parameterPositive largeError) (parameterPositive smallError)
    (min largeError (1 / 4)) (min smallError (1 / 4)) (by positivity) (by positivity)
    (by exact lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    (by exact lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    largeApproximation smallApproximation horizon steps largeDuration smallDuration largeDurationPositive smallDurationPositive
    stepsPositive largeGap clockLarge ((div_le_iff₀ smallDurationPositive).mp clockSmall)
    radius (4 * radius) radiusPositive.le (by linarith) jumpBound
  refine observed.trans (le_trans ?_ total.le)
  gcongr
  · exact min_le_left _ _
  · exact min_le_left _ _

end
end IGSIII34.Diffusion

