import IGSIII34.Diffusion.GreedyExitCountingCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

variable {Vertex Edge Label Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex] [Fintype Label] [MetricSpace Carrier]

def finiteGreedyShortGapCompletion20261011 (embedding : Vertex → Carrier) (radius : ℝ)
    (horizon window step : ℕ) : Set (ℕ → Vertex) :=
  {path | finiteGreedyExitTimeCompletion20261011 embedding radius horizon (step + 1) path ≤ horizon ∧
    finiteGreedyExitTimeCompletion20261011 embedding radius horizon (step + 1) path ≤
      finiteGreedyExitTimeCompletion20261011 embedding radius horizon step path + window}

theorem finiteGreedyShortGap_measurable_completion20261011
    (embedding : Vertex → Carrier) (radius : ℝ) (horizon window step : ℕ) :
    MeasurableSet (finiteGreedyShortGapCompletion20261011 embedding radius horizon window step) := by
  classical
  have firstStopping := (finiteGreedyExitTime_properties_completion20261011 embedding radius horizon step).1
  have lastStopping := (finiteGreedyExitTime_properties_completion20261011 embedding radius horizon (step + 1)).1
  have identity : finiteGreedyShortGapCompletion20261011 embedding radius horizon window step =
      ⋃ start : ℕ, ⋃ last : ℕ, ⋃ (_ : last ≤ horizon), ⋃ (_ : last ≤ start + window),
        {path | (finiteGreedyExitTimeCompletion20261011 embedding radius horizon step path : WithTop ℕ) = start} ∩
        {path | (finiteGreedyExitTimeCompletion20261011 embedding radius horizon (step + 1) path : WithTop ℕ) = last} := by
    ext path
    simp only [finiteGreedyShortGapCompletion20261011, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    norm_cast
    constructor
    · intro bounds
      exact ⟨_, _, bounds.1, bounds.2, rfl, rfl⟩
    · rintro ⟨start, last, before, short, firstEq, lastEq⟩
      exact ⟨lastEq ▸ before, by simpa only [firstEq, lastEq] using short⟩
  rw [identity]
  exact MeasurableSet.iUnion fun start => MeasurableSet.iUnion fun last =>
    MeasurableSet.iUnion fun _before => MeasurableSet.iUnion fun _short =>
      (firstStopping.measurableSpace_le _ (firstStopping.measurableSet_eq' start)).inter
        (lastStopping.measurableSpace_le _ (lastStopping.measurableSet_eq' last))

/-- Each actual greedy short gap is controlled by the previously proved
conditional finite-walk exit estimate, without stationary initialization. -/
theorem finiteDiscreteWalkLaw_greedy_short_gap_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (embedding : Vertex → Carrier) (potentials : Label → Vertex → ℝ)
    (potentialUpper : ∀ label vertex, potentials label vertex ≤ 1)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ label vertex, |rateOneGenerator endpoint (potentials label) vertex| ≤ driftBound)
    (radius error threshold : ℝ) (errorNonnegative : 0 ≤ error) (thresholdBelowOne : threshold < 1)
    (cover : ∀ vertex, ∃ label, 1 - error ≤ potentials label vertex)
    (separating : ∀ label first last, 1 - error ≤ potentials label first →
      radius ≤ dist (embedding first) (embedding last) → potentials label last ≤ threshold)
    (horizon window step : ℕ) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      (finiteGreedyShortGapCompletion20261011 embedding radius horizon window step) ≤
        (Fintype.card Label * (error + window * driftBound)) / (1 - threshold) := by
  classical
  let first := finiteGreedyExitTimeCompletion20261011 embedding radius horizon step
  have properties := finiteGreedyExitTime_properties_completion20261011 embedding radius horizon step
  have escape := finiteDiscreteWalkLaw_cutoff_cover_exit_completion20261011 endpoint positiveDegree initial
    embedding potentials potentialUpper driftBound driftNonnegative generatorBound radius error threshold
    errorNonnegative thresholdBelowOne cover separating (fun path => (first path : WithTop ℕ))
    properties.1 (horizon + 1) window (fun path => by exact_mod_cast properties.2.1 path)
    Set.univ MeasurableSet.univ
  have inclusion : finiteGreedyShortGapCompletion20261011 embedding radius horizon window step ⊆
      Set.univ ∩ {path | ∃ index, ((first path : WithTop ℕ)).untopA ≤ index ∧
        index ≤ ((first path : WithTop ℕ)).untopA + window ∧
        radius ≤ dist (embedding (path ((first path : WithTop ℕ)).untopA)) (embedding (path index))} := by
    intro path member
    have bounds := (finiteGreedyExitTime_properties_completion20261011 embedding radius horizon step).2.2 path
    refine ⟨Set.mem_univ _, finiteGreedyExitTimeCompletion20261011 embedding radius horizon (step + 1) path, ?_, ?_, ?_⟩
    · change first path ≤ finiteGreedyExitTimeCompletion20261011 embedding radius horizon (step + 1) path
      exact bounds
    · change finiteGreedyExitTimeCompletion20261011 embedding radius horizon (step + 1) path ≤ first path + window
      exact member.2
    · change radius ≤ dist (embedding (path (first path)))
        (embedding (path (finiteGreedyExitNextCompletion20261011 embedding radius horizon first path)))
      exact finiteGreedyExitNext_hit_completion20261011 embedding radius horizon first path member.1
  have bound := (mul_le_mul_of_nonneg_left
    (measureReal_mono (μ := finiteDiscreteWalkLaw endpoint positiveDegree initial) inclusion)
    (show 0 ≤ 1 - threshold by linarith)).trans escape
  simp only [probReal_univ, mul_one] at bound
  exact (le_div_iff₀ (show 0 < 1 - threshold by linarith)).mpr (by simpa only [mul_comm] using bound)

theorem finiteDiscreteWalkLaw_greedy_exit_count_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (embedding : Vertex → Carrier) (potentials : Label → Vertex → ℝ)
    (potentialUpper : ∀ label vertex, potentials label vertex ≤ 1)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ label vertex, |rateOneGenerator endpoint (potentials label) vertex| ≤ driftBound)
    (radius error threshold : ℝ) (errorNonnegative : 0 ≤ error) (thresholdBelowOne : threshold < 1)
    (cover : ∀ vertex, ∃ label, 1 - error ≤ potentials label vertex)
    (separating : ∀ label first last, 1 - error ≤ potentials label first →
      radius ≤ dist (embedding first) (embedding last) → potentials label last ≤ threshold)
    (steps horizon window : ℕ) (positiveDenominator : (horizon : ℝ) < steps * window) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      {path | finiteGreedyExitTimeCompletion20261011 embedding radius horizon steps path ≤ horizon} ≤
      (window : ℝ) * steps * ((Fintype.card Label * (error + window * driftBound)) / (1 - threshold)) /
        ((steps : ℝ) * window - horizon) := by
  classical
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  let event := {path | finiteGreedyExitTimeCompletion20261011 embedding radius horizon steps path ≤ horizon}
  let short := finiteGreedyShortGapCompletion20261011 embedding radius horizon window
  have eventMeasurable : MeasurableSet event := by
    have stopping := (finiteGreedyExitTime_properties_completion20261011 embedding radius horizon steps).1
    convert stopping.measurableSpace_le _ (stopping.measurableSet_le' horizon) using 1
    ext path
    dsimp only [event, Set.mem_setOf_eq]
    exact ⟨fun bound => WithTop.coe_le_coe.mpr bound, fun bound => WithTop.coe_le_coe.mp bound⟩
  have countBound := probability_event_from_finite_count_completion20261011 law event eventMeasurable short
    (finiteGreedyShortGap_measurable_completion20261011 embedding radius horizon window) steps
    ((steps : ℝ) * window - horizon) window
    ((Fintype.card Label * (error + window * driftBound)) / (1 - threshold))
    (Nat.cast_nonneg _) (fun path member => by
      have monotone : Monotone (fun step => finiteGreedyExitTimeCompletion20261011 embedding radius horizon step path) :=
        monotone_nat_of_le_succ fun step =>
          (finiteGreedyExitTime_properties_completion20261011 embedding radius horizon step).2.2 path
      simpa only [short, finiteGreedyShortGapCompletion20261011, Set.indicator_apply, Set.mem_setOf_eq] using
        increasing_times_short_gap_count_completion20261011
          (fun step => finiteGreedyExitTimeCompletion20261011 embedding radius horizon step path) monotone steps horizon window member)
    (fun step _ => finiteDiscreteWalkLaw_greedy_short_gap_completion20261011 endpoint positiveDegree initial
      embedding potentials potentialUpper driftBound driftNonnegative generatorBound radius error threshold
      errorNonnegative thresholdBelowOne cover separating horizon window step)
  exact (le_div_iff₀ (show 0 < (steps : ℝ) * window - horizon by linarith)).mpr
    (by simpa only [mul_comm] using countBound)

end
end IGSIII34.Diffusion
