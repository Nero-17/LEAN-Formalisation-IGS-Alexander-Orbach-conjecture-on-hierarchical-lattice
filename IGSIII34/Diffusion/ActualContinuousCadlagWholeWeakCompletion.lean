import IGSIII34.Diffusion.ActualContinuousGlobalWholeWeakCompletion
import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology BigOperators NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance actualWholeContinuousCadlagCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualWholeContinuousCadlagCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualWholeContinuousCadlagCompletionCompact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualWholeContinuousCadlagCompletionMeasurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualWholeContinuousCadlagCompletionBorel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualWholeContinuousCadlagNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualWholeContinuousCadlagCutoffApproximationCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualWholeContinuousCadlagNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualWholeContinuousCadlagTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualWholeContinuousCadlagNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualWholeContinuousCadlagInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualWholeContinuousCadlagCompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

/-- The exact original exponential-holding finite law on genuine cadlag paths. -/
def finiteContinuousCadlagProbabilityCompletion
    {Vertex Edge Space : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [DecidableEq Vertex] [Fintype Edge] [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion Space) :=
  holdingCadlagProbabilityCompletion
    (⟨finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex), inferInstance⟩ :
      ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    ((finiteContinuousWalkSampleLaw_regular endpoint positiveDegree (initial : Measure Vertex)).mono
      (fun sample clock => ⟨clock.1, clock.2.1⟩)) scale scalePositive placement

theorem finiteContinuousCadlagProbability_val_completion
    {Vertex Edge Space : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [DecidableEq Vertex] [Fintype Edge] [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (finiteContinuousCadlagProbabilityCompletion endpoint positiveDegree initial scale scalePositive placement).map
      measurable_subtype_coe.aemeasurable =
      finiteContinuousGlobalSkorokhodProbabilityCompletion endpoint positiveDegree initial scale scalePositive placement := by
  exact holdingCadlagProbability_val_completion _ _ _ _ _

def actualPaperContinuousElectricalCadlagLawCompletion
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (depth : ℕ) : ProbabilityMeasure (SkorokhodCadlagPathCompletion
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) :=
  finiteContinuousCadlagProbabilityCompletion
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
    (initial depth)
    (actualPaperDiscreteClockCompletion rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth)
    (actualPaperDiscreteClock_positive_completion rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ depth)
    (fun vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ depth vertex)

theorem actualPaperContinuousElectricalCadlagLaw_val_completion
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (depth : ℕ) :
    (actualPaperContinuousElectricalCadlagLawCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive initial depth).map measurable_subtype_coe.aemeasurable =
      actualPaperContinuousElectricalGlobalJ1LawCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive initial depth := by
  exact finiteContinuousCadlagProbability_val_completion _ _ _ _ _ _
include anchor in
/-- Whole-sequence genuine interval J1 convergence follows from the
actual finite resolvents and original walk law. The only convergence
input is the initial distribution in the common electrical carrier. -/
theorem actual_continuous_cadlag_whole_weak_convergence_completion
    (edgePositive : 0 < rule.edges) (growthGreaterThanOne : 1 < growth)
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times)
    (initialLimit : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (initialConvergence : Tendsto (fun depth => (initial depth).map
      (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)).aemeasurable)
      atTop (𝓝 initialLimit)) :
    ∃ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩),

        Tendsto (fun depth => actualPaperContinuousElectricalCadlagLawCompletion rule p positive belowOne fixedPoint
          growth value growthPositive marks chemicalScale chemicalScalePositive initial depth) atTop
          (𝓝 (continuousCadlagProbabilityCompletion limitLaw (countableTimeContinuousSampleCompletion times dense) (countableTimeContinuousSample_continuous_completion times dense) (countableTimeContinuousSample_evaluation_measurable_completion times dense))) := by
  obtain ⟨limitLaw, weak⟩ := actual_continuous_global_skorokhod_whole_weak_convergence_completion
    rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor
    edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBound data initial times timeZero dense initialLimit initialConvergence
  refine ⟨limitLaw, ?_⟩
  apply probability_subtype_weak_of_val_weak_completion
    (fun path : SkorokhodGlobalPathCompletion
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) =>
      SkorokhodCadlagCompletion path)
  simpa only [actualPaperContinuousElectricalCadlagLaw_val_completion,
    continuousCadlagProbability_val_completion] using weak

end
end IGSIII34.Diffusion