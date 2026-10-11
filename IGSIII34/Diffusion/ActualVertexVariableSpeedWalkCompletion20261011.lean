import IGSIII34.Diffusion.WeightedClockRateIdentificationCompletion20261011
import IGSIII34.Diffusion.FiniteWeightedGlobalWeakCompletion20261011
import IGSIII34.Diffusion.ActualPaperClockWalkCompletion20261011
import IGSIII34.ResistanceLimit.ActualStationaryCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})

local instance vertexSpeedCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance vertexSpeedCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

def actualVertexVariableSpeedGlobalSampleCompletion20261011 (depth : ℕ)
    (sample : (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) × (ℕ → ℝ)) :
    SkorokhodGlobalPathCompletion20261011 (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) :=
  weightedHoldingGlobalSampleCompletion20261011
    (finiteCountingClockDensityCompletion20261011 (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)))
    (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth+1))
    (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth) sample

def actualVertexVariableSpeedGlobalLawCompletion20261011 (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ProbabilityMeasure (SkorokhodGlobalPathCompletion20261011 (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)
  exact finiteWeightedGlobalSkorokhodProbabilityCompletion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (Space := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)) initial
    (finiteCountingClockDensityCompletion20261011 (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)))
    (finiteCountingClockDensity_positive_completion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
        (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)))
    (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth+1))
    (by positivity) (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth)
theorem actualVertexVariableSpeedGlobalSample_vertex_clock_completion20261011 (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ∀ᵐ sample ∂(finiteContinuousWalkSampleLaw (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
        (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)) (initial : Measure _)),
      ∀ time : ℝ≥0,
        (actualVertexVariableSpeedGlobalSampleCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
          chemicalScale chemicalScalePositive depth sample).toFun time =
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth
          (holdingTimePath sample.1
            (fun index => sample.2 index / degree (clusterRetainedEndpoint (rule.generation depth).network
              (stationaryConfiguration rule marks.val depth)) (sample.1 index))
            ((Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) : ℝ) * growth ^ (depth+1) * time)) := by
  unfold actualVertexVariableSpeedGlobalSampleCompletion20261011
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)
  have identity := finiteCountingClockDensity_vertex_clock_identity_completion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)) initial
    (growth ^ (depth+1)) (pow_pos growthPositive _)
  filter_upwards [identity] with sample identity
  intro time
  exact congrArg (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth)
    (identity time time.property)

end
end IGSIII34.Diffusion
