import IGSIII34.Diffusion.StationaryDegreeWalkCompletion
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Metrizable.Uniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

/-- A law on all countably many observation times has a weakly convergent
subsequence. The product topology is used; continuous sample paths are a
separate conclusion and are not assumed here. -/
theorem countableTimeLaws_subsequence_completion
    (laws : ℕ → ProbabilityMeasure (ℕ → Space)) :
    ∃ limitLaw : ProbabilityMeasure (ℕ → Space), ∃ selectedDepth : ℕ → ℕ,
      StrictMono selectedDepth ∧
      Tendsto (fun index => laws (selectedDepth index)) atTop (𝓝 limitLaw) := by
  obtain ⟨limitLaw, _, selectedDepth, selectedStrict, convergence⟩ :=
    (isCompact_univ (X := ProbabilityMeasure (ℕ → Space))).tendsto_subseq
      (x := laws) (fun _ => Set.mem_univ _)
  exact ⟨limitLaw, selectedDepth, selectedStrict, convergence⟩

/-- Convergence of a countable-time skeleton law gives convergence of every
finite-dimensional distribution, simultaneously and without another
subsequence extraction. -/
theorem countableTimeLaws_finite_marginals_completion
    (laws : ℕ → ProbabilityMeasure (ℕ → Space))
    (limitLaw : ProbabilityMeasure (ℕ → Space))
    (convergence : Tendsto laws atTop (𝓝 limitLaw))
    {count : ℕ} (coordinates : Fin count → ℕ) :
    Tendsto (fun depth => (laws depth).map
      (show AEMeasurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates index))
        (laws depth) from (by fun_prop : Measurable _).aemeasurable))
      atTop (𝓝 (limitLaw.map
        (show AEMeasurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates index))
          limitLaw from (by fun_prop : Measurable _).aemeasurable))) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    laws limitLaw convergence (by fun_prop)

/-- The single-time law of any extracted skeleton limit is determined by
the whole-sequence marginal limit. No Markov or path-continuity hypothesis
is hidden in this identification. -/
theorem countableTimeLaws_limit_marginal_completion
    (laws : ℕ → ProbabilityMeasure (ℕ → Space))
    (limitLaw : ProbabilityMeasure (ℕ → Space))
    (selectedDepth : ℕ → ℕ) (selectedDiverges : Tendsto selectedDepth atTop atTop)
    (convergence : Tendsto (fun index => laws (selectedDepth index)) atTop (𝓝 limitLaw))
    (coordinate : ℕ) (marginal : ProbabilityMeasure Space)
    (marginalConvergence : Tendsto (fun depth => (laws depth).map
      (measurable_pi_apply coordinate).aemeasurable) atTop (𝓝 marginal)) :
    limitLaw.map (measurable_pi_apply coordinate).aemeasurable = marginal := by
  exact tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun index => laws (selectedDepth index)) limitLaw convergence (continuous_apply coordinate))
    (marginalConvergence.comp selectedDiverges)

def countableTimeObservation {Vertex : Type*} (times : ℕ → ℝ≥0)
    (inclusion : Vertex → Space) (path : ℝ≥0 → Vertex) : ℕ → Space :=
  fun coordinate => inclusion (path (times coordinate))

theorem countableTimeObservation_measurable {Vertex : Type*}
    [MeasurableSpace Vertex] (times : ℕ → ℝ≥0)
    (inclusion : Vertex → Space) (inclusionMeasurable : Measurable inclusion) :
    Measurable (countableTimeObservation times inclusion) := by
  apply measurable_pi_lambda
  intro coordinate
  exact inclusionMeasurable.comp (measurable_pi_apply (times coordinate))

/-- Pushforward of the genuine continuous-time walk law under a single
spatial inclusion and countably many observations. -/
def observedWalkProbabilityLaw {Vertex : Type*} [MeasurableSpace Vertex]
    (law : Measure (ℝ≥0 → Vertex)) [IsProbabilityMeasure law]
    (times : ℕ → ℝ≥0) (inclusion : Vertex → Space)
    (inclusionMeasurable : Measurable inclusion) : ProbabilityMeasure (ℕ → Space) :=
  ⟨law.map (countableTimeObservation times inclusion),
    isProbabilityMeasure_map (countableTimeObservation_measurable times inclusion inclusionMeasurable).aemeasurable⟩

theorem observedWalkProbabilityLaw_marginal {Vertex : Type*} [MeasurableSpace Vertex]
    (law : Measure (ℝ≥0 → Vertex)) [IsProbabilityMeasure law]
    (times : ℕ → ℝ≥0) (inclusion : Vertex → Space)
    (inclusionMeasurable : Measurable inclusion) (coordinate : ℕ) :
    ((observedWalkProbabilityLaw law times inclusion inclusionMeasurable).map
      (measurable_pi_apply coordinate).aemeasurable : Measure Space) =
      (law.map (fun path => path (times coordinate))).map inclusion := by
  change (law.map (countableTimeObservation times inclusion)).map
    (fun path : ℕ → Space => path coordinate) = _
  rw [Measure.map_map (measurable_pi_apply coordinate)
    (countableTimeObservation_measurable times inclusion inclusionMeasurable),
    Measure.map_map inclusionMeasurable (measurable_pi_apply (times coordinate))]
  rfl

end
end IGSIII34.Diffusion
