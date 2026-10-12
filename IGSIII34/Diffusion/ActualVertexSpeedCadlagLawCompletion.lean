import IGSIII34.Diffusion.FiniteWeightedCadlagLawCompletion
import IGSIII34.Diffusion.ActualVertexVariableSpeedWalkCompletion
import IGSIII34.Diffusion.WeightedClockRateIdentificationCompletion
import IGSIII34.Diffusion.ActualPaperClockWalkCompletion
import IGSIII34.ResistanceLimit.ActualStationaryCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})

local instance vertexCadlagCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance vertexCadlagCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

def actualVertexVariableSpeedCadlagLawCompletion (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)
  let endpoint := clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let degreePositive := cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)
  exact finiteWeightedCadlagProbabilityCompletion
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    endpoint degreePositive initial
    (finiteCountingClockDensityCompletion
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) endpoint)
    (finiteCountingClockDensity_positive_completion
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) endpoint degreePositive)
    (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth+1))
    (by positivity) (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth)

theorem actualVertexVariableSpeedCadlagLaw_val_completion (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    (actualVertexVariableSpeedCadlagLawCompletion rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive depth initial).map
      measurable_subtype_coe.aemeasurable =
      actualVertexVariableSpeedGlobalLawCompletion rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive depth initial := by
  unfold actualVertexVariableSpeedCadlagLawCompletion
  rw [finiteWeightedCadlagProbability_val_completion]
  apply Subtype.ext
  rfl

end
end IGSIII34.Diffusion
