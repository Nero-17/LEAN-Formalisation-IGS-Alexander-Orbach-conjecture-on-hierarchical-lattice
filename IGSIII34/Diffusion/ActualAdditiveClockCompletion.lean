import IGSIII34.Diffusion.ResolventAdditiveClockConvergenceCompletion
import IGSIII34.Diffusion.ActualCountingClockDensityCompletion
import IGSIII34.Diffusion.ActualPaperClockWalkCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology BigOperators

theorem actual_additive_clock_prefix_probability_tendsto_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (growth : ℝ) (growthPositive : 0 < growth)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth))
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBound : ∀ depth vertex,
      |actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth vertex| ≤ bound)
    (correctorsVanish : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth,
        |actualPaperClockGraphResolventCompletion rule (stationaryConfiguration rule marks)
          (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true)
          chemicalScale chemicalScalePositive depth growth growthPositive 1 zero_lt_one
          (actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth) vertex| < tolerance)
    (horizon radius : ℝ) (horizonNonnegative : 0 ≤ horizon) (radiusPositive : 0 < radius) :
    Tendsto (fun depth =>
      (finiteDiscreteWalkLaw (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth))
        (cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks depth)
          (markedGenerationConfiguration_crosses rule marks crossing depth [] true)) (initial depth : Measure _)).real
        {path | ∃ prefixLength ≤ ⌊(2 * Fintype.card (ClusterEdge (rule.generation depth).network
            (stationaryConfiguration rule marks depth)) * growth ^ (depth+1)) * horizon⌋₊,
          radius ≤ |finiteWalkScaledAdditiveCompletion
            (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth)) * growth ^ (depth+1))
            (actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth)
            prefixLength path|}) atTop (𝓝 0) := by
  let vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth
  let edges := fun depth => ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth)
  let endpoint := fun depth => clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)
  let degreePositive := fun depth => cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks depth)
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
  let clocks := fun depth => 2 * Fintype.card (edges depth) * growth ^ (depth+1)
  have clocksPositive (depth : ℕ) : 0 < clocks depth := by
    letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks depth)
      (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
    have edgeCard : 0 < Fintype.card (edges depth) := Fintype.card_pos
    dsimp only [clocks]
    positivity
  letI : ∀ depth, Nonempty (vertices depth) := fun depth =>
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI : ∀ depth, MeasurableSpace (vertices depth) := fun depth =>
    actualFiniteClusterMeasurableSpace rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth
  let forcing := actualCountingClockCenteredForcingCompletion rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive
  apply finiteGraphResolvent_additive_prefix_probability_tendsto_completion
    vertices edges endpoint degreePositive initial 1 zero_lt_one clocks clocksPositive forcing bound boundNonnegative forcingBound
    ?_ horizon radius horizonNonnegative radiusPositive
  intro tolerance positive
  filter_upwards [correctorsVanish tolerance positive] with depth small
  intro vertex
  letI : Nonempty (vertices depth) := ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks depth)
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
  exact small vertex

end
end IGSIII34.Diffusion
