import IGSIII34.Diffusion.GreedyExitModulusCompletion

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

variable {Vertex Edge LabelLarge LabelSmall Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex] [Fintype LabelLarge] [Fintype LabelSmall] [MetricSpace Carrier]

/-- A quantitative actual finite-walk modulus bound obtained by greedy
exit counting and two independent separating covers and stopping windows. No path-tightness assertion is
supplied as an input, and the initialization is arbitrary. -/
theorem finiteDiscreteWalkLaw_two_cover_modulus_probability_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (embedding : Vertex → Carrier) (potentials : LabelLarge → Vertex → ℝ)
    (potentialUpper : ∀ label vertex, potentials label vertex ≤ 1)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ label vertex, |rateOneGenerator endpoint (potentials label) vertex| ≤ driftBound)
    (radius error threshold : ℝ) (radiusPositive : 0 < radius)
    (errorNonnegative : 0 ≤ error) (thresholdBelowOne : threshold < 1)
    (cover : ∀ vertex, ∃ label, 1 - error ≤ potentials label vertex)
    (separating : ∀ label first last, 1 - error ≤ potentials label first →
      radius ≤ dist (embedding first) (embedding last) → potentials label last ≤ threshold)
    (smallPotentials : LabelSmall → Vertex → ℝ)
    (smallPotentialUpper : ∀ label vertex, smallPotentials label vertex ≤ 1)
    (smallDrift : ℝ) (smallDriftNonnegative : 0 ≤ smallDrift)
    (smallGeneratorBound : ∀ label vertex, |rateOneGenerator endpoint (smallPotentials label) vertex| ≤ smallDrift)
    (smallError smallThreshold : ℝ) (smallErrorNonnegative : 0 ≤ smallError) (smallThresholdBelowOne : smallThreshold < 1)
    (smallCover : ∀ vertex, ∃ label, 1 - smallError ≤ smallPotentials label vertex)
    (smallSeparating : ∀ label first last, 1 - smallError ≤ smallPotentials label first →
      radius ≤ dist (embedding first) (embedding last) → smallPotentials label last ≤ smallThreshold)
    (steps horizon largeWindow smallWindow : ℕ)
    (positiveDenominator : (horizon : ℝ) < steps * largeWindow)
    (jump : ℝ) (jumpNonnegative : 0 ≤ jump)
    (jumpBound : ∀ᵐ path ∂finiteDiscreteWalkLaw endpoint positiveDegree initial,
      ∀ index < horizon, dist (embedding (path index)) (embedding (path (index + 1))) ≤ jump) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      {path | ∃ first last, first ≤ last ∧ last ≤ horizon ∧ last ≤ first + smallWindow ∧
        3 * radius + jump < dist (embedding (path first)) (embedding (path last))} ≤
      (largeWindow : ℝ) * steps *
        ((Fintype.card LabelLarge * (error + largeWindow * driftBound)) / (1 - threshold)) /
          ((steps : ℝ) * largeWindow - horizon) +
      steps * ((Fintype.card LabelSmall * (smallError + smallWindow * smallDrift)) / (1 - smallThreshold)) := by
  classical
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  let excessive := {path | finiteGreedyExitTimeCompletion embedding radius horizon steps path ≤ horizon}
  let short := finiteGreedyShortGapCompletion embedding radius horizon smallWindow
  have inclusion : ∀ᵐ path ∂law,
      (path ∈ {path | ∃ first last, first ≤ last ∧ last ≤ horizon ∧ last ≤ first + smallWindow ∧
        3 * radius + jump < dist (embedding (path first)) (embedding (path last))}) →
        path ∈ excessive ∪ ⋃ step : Fin steps, short step := by
    filter_upwards [jumpBound] with path jumps
    intro bad
    by_cases many : path ∈ excessive
    · exact Or.inl many
    · by_cases someShort : ∃ step : Fin steps, path ∈ short step
      · exact Or.inr (Set.mem_iUnion.mpr someShort)
      · have noShort : ∀ step < steps, path ∉ finiteGreedyShortGapCompletion embedding radius horizon smallWindow step := by
          intro step before member
          exact someShort ⟨⟨step, before⟩, member⟩
        obtain ⟨first, last, ordered, before, window, far⟩ := bad
        have bound := finiteGreedyExitTime_modulus_completion embedding radius radiusPositive
          steps horizon smallWindow path jump jumpNonnegative jumps (not_le.mp many) noShort first last ordered before window
        exact False.elim (not_lt_of_ge bound far)
  have outer := ENNReal.toReal_mono (measure_ne_top law (excessive ∪ ⋃ step : Fin steps, short step))
    (measure_mono_ae inclusion)
  have split := measureReal_union_le (μ := law) excessive (⋃ step : Fin steps, short step)
  have count := finiteDiscreteWalkLaw_greedy_exit_count_completion endpoint positiveDegree initial
    embedding potentials potentialUpper driftBound driftNonnegative generatorBound radius error threshold
    errorNonnegative thresholdBelowOne cover separating steps horizon largeWindow positiveDenominator
  have shortProbability := probability_first_short_gap_union_completion law short steps
    ((Fintype.card LabelSmall * (smallError + smallWindow * smallDrift)) / (1 - smallThreshold))
    (fun step _ => finiteDiscreteWalkLaw_greedy_short_gap_completion endpoint positiveDegree initial
      embedding smallPotentials smallPotentialUpper smallDrift smallDriftNonnegative smallGeneratorBound radius smallError smallThreshold
      smallErrorNonnegative smallThresholdBelowOne smallCover smallSeparating horizon smallWindow step)
  exact (outer.trans split).trans (add_le_add count shortProbability)

end
end IGSIII34.Diffusion

