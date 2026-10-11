import IGSIII34.Diffusion.FiniteResolventExitCompletion20261011
import IGSIII34.Diffusion.NaturalClockWalkLaws

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry MeasureTheory ProbabilityTheory
open scoped Topology NNReal

variable (rule : Rule)
  (configuration : ∀ depth, Configuration (rule.generation depth).edges)
  (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

/-- The library's generation zero is the first replacement of the one-edge
graph. The manuscript generation and resistance clock are therefore
depth plus one. Existing auxiliary depth-indexed clocks are untouched. -/
def actualPaperClockDegreeWalkLawCompletion20261011 (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth)
    (resistance : ℝ≥0) : Measure (ℝ≥0 → ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth) :=
  naturalDegreeWalkLaw (Vertex := ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (Measure.dirac initial) resistance (depth + 1)

instance actualPaperClockDegreeWalkLaw_probability_completion20261011 (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth)
    (resistance : ℝ≥0) :
    IsProbabilityMeasure (actualPaperClockDegreeWalkLawCompletion20261011 rule configuration crossing
      chemicalScale chemicalScalePositive depth initial resistance) := by
  unfold actualPaperClockDegreeWalkLawCompletion20261011
  infer_instance

def actualPaperClockGraphResolventCompletion20261011 (depth : ℕ)
    (resistance : ℝ) (resistancePositive : 0 < resistance)
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (forcing : ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth → ℝ) :
    ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth → ℝ :=
  finiteGraphResolvent (Vertex := ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    parameter (2 * Fintype.card (ClusterEdge (rule.generation depth).network (configuration depth)) * resistance ^ (depth + 1))
    parameterPositive (by positivity) forcing

/-- Exact full-cluster exit estimate with the manuscript generation clock. -/
theorem actualPaperClockGraphResolvent_exit_bound_completion20261011 (depth : ℕ)
    (resistance : ℝ) (resistancePositive : 0 < resistance)
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (forcing : ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth → ℝ)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ parameter)
    (initial : ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth)
    (exitSet : Set (ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth))
    (initialError threshold horizon : ℝ) (thresholdBelowOne : threshold < 1)
    (horizonNonnegative : 0 ≤ horizon) (time : ℕ)
    (timeBound : (time : ℝ) ≤
      (2 * (rule.generation depth).network.liveCount .connected .connected (configuration depth) *
        resistance ^ (depth + 1)) * horizon)
    (initialBound : 1 - initialError ≤ actualPaperClockGraphResolventCompletion20261011 rule configuration crossing
      chemicalScale chemicalScalePositive depth resistance resistancePositive parameter parameterPositive forcing initial)
    (exitBound : ∀ vertex ∈ exitSet, actualPaperClockGraphResolventCompletion20261011 rule configuration crossing
      chemicalScale chemicalScalePositive depth resistance resistancePositive parameter parameterPositive forcing vertex ≤ threshold) :
    (1 - threshold) * (actualFiniteDiscreteWalkLaw rule configuration crossing chemicalScale chemicalScalePositive depth initial).real
      {path | ∃ index ≤ time, path index ∈ exitSet} ≤ initialError + 2 * parameter * horizon := by
  letI := clusterEdge_nonempty (rule.generation depth).network (configuration depth) (crossing depth)
  apply finiteGraphResolvent_natural_exit_bound_completion20261011
    (Vertex := ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    parameter (resistance ^ (depth + 1)) parameterPositive (pow_pos resistancePositive _)
    forcing forcingBound initial exitSet initialError threshold horizon thresholdBelowOne horizonNonnegative time
  · simpa only [clusterEdge_card] using timeBound
  · exact initialBound
  · exact exitBound

end
end IGSIII34.Diffusion
