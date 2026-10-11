import IGSIII34.Diffusion.ActualCommonDiscreteChemicalCadlagCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2400000
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

variable {Ambient : Type*} [MetricSpace Ambient] [CompactSpace Ambient]
  [MeasurableSpace Ambient] [BorelSpace Ambient]

/-- The original discrete simple walk at the paper clock, placed in an
arbitrary actual common realization. -/
def actualPaperPlacedDiscreteCadlagLaw
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth → Ambient) (depth : ℕ) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Ambient) :=
  discreteCadlagProbabilityCompletion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (⟨finiteDiscreteWalkLaw
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
      (initial depth : Measure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)),
      inferInstance⟩ : ProbabilityMeasure (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
        chemicalScale chemicalScalePositive depth))
    (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩ depth)
    (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val,marks.property.1.1⟩ depth)
    (sources depth)

local instance actualCommonPaperElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := borel _
local instance actualCommonPaperElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)]

theorem actualPaperPlacedDiscreteCadlagLaw_tendsto
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
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive initial depth) atTop (𝓝 law)) :
    Tendsto (fun depth => actualPaperPlacedDiscreteCadlagLaw rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive initial sources depth) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding continuous).measurable.aemeasurable)) := by
  exact discreteCadlagProbability_common_embedding_weak_completion20261011
    (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (fun depth => (⟨finiteDiscreteWalkLaw
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
      (initial depth : Measure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)),
      inferInstance⟩ : ProbabilityMeasure (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)))
    (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    targetEmbedding continuous
    (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth)
    sources law weak placementClose

end
end IGSIII34.ResistanceLimit
