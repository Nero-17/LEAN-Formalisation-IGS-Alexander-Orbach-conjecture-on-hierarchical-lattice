import IGSIII34.Diffusion.ActualNaturalClockRescaleSameLimit
import IGSIII34.Diffusion.ActualPaperDeterministicLawIdentityCompletion20261011
import IGSIII34.Diffusion.FiniteWeightedCommonEmbeddingCompletion20261011
import IGSIII34.Diffusion.UsualLocalJ1PathLaw
import IGSIII34.Diffusion.UsualLocalJ1SpatialWeakTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII34.Spectral
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
  (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
  (growth : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
variable {Ambient : Type*} [MetricSpace Ambient] [CompactSpace Ambient]
  [MeasurableSpace Ambient] [BorelSpace Ambient]

/-- The deterministic paper-clock original finite walk placed through
the prescribed finite-source embedding into the same common ambient. -/
def actualPaperDeterministicPlacedCadlagLaw
    (countingSpeed : Bool) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (placement : ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth → Ambient) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Ambient) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  exact finiteWeightedCadlagProbabilityCompletion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) initial
    (fun vertex => if countingSpeed then finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) vertex else 1)
    (by intro vertex; cases countingSpeed
        · exact zero_lt_one
        · exact finiteCountingClockDensity_positive_completion20261011
            (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) _
            (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) vertex)
    (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth *
      (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed depth : ℝ))
    (mul_pos (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ depth) (NNReal.coe_pos.mpr
        (actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint
          growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth))) placement

local instance deterministicCommonElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance deterministicCommonElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]

/-- Transport the deterministic-clock limit to the already prescribed
common ambient, preserving the exact law and spatial embedding. -/
theorem actualPaperDeterministicPlacedCadlagLaw_tendsto
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth → Ambient)
    (targetEmbedding : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ → Ambient) (continuous : Continuous targetEmbedding)
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ point,
      dist (sources depth point) (targetEmbedding (actualStationaryElectricalVertex rule p positive belowOne fixedPoint
        growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth point)) < tolerance)
    (countingSpeed : Bool)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (weak : Tendsto (fun depth => actualPaperDeterministicCadlagLawCompletion20261011 rule classicalRule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth (initial depth)) atTop (𝓝 law)) :
    Tendsto (fun depth => actualPaperDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive countingSpeed depth (initial depth) (sources depth)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding continuous).measurable.aemeasurable)) := by
  letI : ∀ depth, Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    fun depth => ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI : ∀ depth, Nonempty (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :=
    fun depth => clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  have projected : Tendsto (fun depth => finiteWeightedCadlagProbabilityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial depth)
      (fun vertex => if countingSpeed then finiteCountingClockDensityCompletion20261011
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) vertex else 1)
      (by intro vertex; cases countingSpeed
          · exact zero_lt_one
          · exact finiteCountingClockDensity_positive_completion20261011
              (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) _
              (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) vertex)
      (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth *
        (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed depth : ℝ))
      (mul_pos (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ depth) (NNReal.coe_pos.mpr
          (actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint
            growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth)))
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth))
      atTop (𝓝 law) := by
    simpa only [actualPaperDeterministicCadlagLawCompletion20261011,
      actualWeightedClockRescaledCadlagLawCompletion20261011] using weak
  exact finiteWeightedCadlagProbability_common_embedding_weak_completion20261011
    (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (fun depth => ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (fun depth => clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (fun depth => cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) initial
    (fun depth vertex => if countingSpeed then finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) vertex else 1)
    (fun depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) => by
      cases countingSpeed
      · exact zero_lt_one
      · exact finiteCountingClockDensity_positive_completion20261011
          (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) _
          (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) vertex)
    (fun depth => actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth *
      (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed depth : ℝ))
    (fun depth => mul_pos (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ depth) (NNReal.coe_pos.mpr
        (actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint
          growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth)))
    targetEmbedding continuous
    (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth)
    sources law projected placementClose

end
end IGSIII34.Diffusion
