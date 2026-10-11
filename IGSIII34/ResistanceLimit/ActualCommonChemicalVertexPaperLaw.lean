import IGSIII34.ResistanceLimit.ActualPaperCadlagSameLaw
import IGSIII34.Diffusion.ActualCommonVertexSpeedChemicalCadlagCompletion20261011
import IGSIII34.Diffusion.ActualVertexSpeedGlobalWeakCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
local instance actualCommonVertexPaperElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := borel _
local instance actualCommonVertexPaperElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)]

theorem actual_vertex_cadlag_same_law
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩))
    (weak : Tendsto (fun depth => actualVertexVariableSpeedGlobalLawCompletion20261011
      rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩
      chemicalScale chemicalScalePositive depth (initial depth)) atTop
      (𝓝 (limitLaw.map (continuousGlobalFamily_measurable_completion20261011
        (countableTimeContinuousSampleCompletion20261011 times dense)
        (countableTimeContinuousSample_continuous_completion20261011 times dense)
        (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).aemeasurable))) :
    Tendsto (fun depth => actualVertexVariableSpeedCadlagLawCompletion20261011
      rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩
      chemicalScale chemicalScalePositive depth (initial depth)) atTop
      (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw
        (countableTimeContinuousSampleCompletion20261011 times dense)
        (countableTimeContinuousSample_continuous_completion20261011 times dense)
        (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense))) := by
  apply probability_subtype_weak_of_val_weak_completion20261011
    (fun path : SkorokhodGlobalPathCompletion20261011
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩) => SkorokhodCadlagCompletion20261011 path)
  simp only [continuousCadlagProbability_val_completion20261011]
  convert weak using 1
  funext depth
  exact actualVertexVariableSpeedCadlagLaw_val_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive ⟨marks.val,marks.property.1.1⟩ chemicalScale chemicalScalePositive depth (initial depth)

variable {Ambient : Type*} [MetricSpace Ambient] [CompactSpace Ambient]
  [MeasurableSpace Ambient] [BorelSpace Ambient]

/-- The actual walk with rate one per incident edge transfers to the fixed
common ambient, preserving its already constructed limit law. -/
theorem actualVertexPlacedCadlagLaw_tendsto
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth → Ambient)
    (targetEmbedding : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val,marks.property.1.1⟩ → Ambient) (continuous : Continuous targetEmbedding)
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ point,
      dist (sources depth point) (targetEmbedding (actualStationaryElectricalVertex rule p positive belowOne fixedPoint
        growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth point)) < tolerance)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)))
    (weak : Tendsto (fun depth => actualVertexVariableSpeedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩ chemicalScale chemicalScalePositive depth (initial depth)) atTop (𝓝 law)) :
    Tendsto (fun depth => actualVertexVariableSpeedPlacedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive depth (initial depth) (sources depth)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding continuous).measurable.aemeasurable)) := by
  letI : ∀ depth, Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    fun depth => ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  let endpoint := fun depth => clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let degreePositive := fun depth => cluster_degree_positive _ _
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  letI : ∀ depth, Nonempty (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :=
    fun depth => clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  exact finiteWeightedCadlagProbability_common_embedding_weak_completion20261011
    (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (fun depth => ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    endpoint degreePositive initial
    (fun depth => finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) (endpoint depth))
    (fun depth => finiteCountingClockDensity_positive_completion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (endpoint depth) (degreePositive depth))
    (fun depth => 2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth + 1))
    (fun depth => by positivity) targetEmbedding continuous
    (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val,marks.property.1.1⟩ depth)
    sources law weak placementClose

end
end IGSIII34.ResistanceLimit
