import IGSIII34.Diffusion.CountableTimeLimitsCompletion20261011
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion20261011
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter ProbabilityTheory
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

local instance actualDiscreteObservationMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance actualDiscreteObservationBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

/-- Exact manuscript acceleration for the actual retained cluster, whose
library generation depth corresponds to manuscript generation depth+1. -/
def actualPaperDiscreteClockCompletion20261011 (depth : ℕ) : ℝ :=
  2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth + 1)

/-- Genuine accelerated jump-chain observations, at all countably many
specified times, placed at the canonical electrical birth vertices. -/
def actualPaperDiscreteElectricalObservationLawCompletion20261011
    (times : ℕ → ℝ≥0)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (depth : ℕ) : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  let law := finiteDiscreteWalkLaw (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)) (initial depth)
  let observation := fun (path : ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) coordinate =>
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth
      (path ⌊actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value marks depth * (times coordinate : ℝ)⌋₊)
  have measurable : Measurable observation := by
    apply measurable_pi_lambda
    intro coordinate
    exact (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)).comp (measurable_pi_apply _)
  exact ⟨law.map observation, Measure.isProbabilityMeasure_map measurable.aemeasurable⟩

/-- Compact countable-law subsequences are obtained from the actual walk.
Path continuity and Markov identification are subsequent proved obligations. -/
theorem actualPaperDiscreteElectricalObservation_subsequence_completion20261011
    [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]
    (times : ℕ → ℝ≥0)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ∃ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks),
      ∃ selected : ℕ → ℕ, StrictMono selected ∧
      Tendsto (fun index => actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive times initial (selected index)) atTop (𝓝 limitLaw) :=
  countableTimeLaws_subsequence_completion20261011 _

end
end IGSIII34.Diffusion

