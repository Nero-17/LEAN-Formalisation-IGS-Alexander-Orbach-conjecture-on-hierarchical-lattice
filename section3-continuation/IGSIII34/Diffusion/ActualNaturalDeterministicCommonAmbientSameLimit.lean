import IGSIII34.Diffusion.ActualPaperDeterministicCommonAmbient
import IGSIII34.Diffusion.ActualWeightedClockRescaleCompletion20261011
import IGSIII34.Diffusion.ActualVertexSpeedGlobalWeakCompletion20261011
import IGSIII34.Diffusion.ActualNaturalAdditiveClockCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteGlobalWholeWeakCompletion20261011
import IGSIII34.Diffusion.ActualContinuousLimitAssemblyCompletion20261011
import IGSIII34.Diffusion.ActualNaturalDegreeMassCompletion20261011
import IGSIII34.Diffusion.ActualResolventUniformCompletion20261011
import IGSIII34.Spectral.ActualNaturalSpectralWitnessCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII34.Spectral
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance sameAmbientNaturalClockRescaleCompletionMeasurableCompletion20261011 {Carrier : Type*} [UniformSpace Carrier] : MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance sameAmbientNaturalClockRescaleCompletionBorelCompletion20261011 {Carrier : Type*} [UniformSpace Carrier] : BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- The original natural field supplies all electrical convergence and mesh
inputs. Any actual Perron boundary realization with the same vertex ratios
therefore has whole finite-resolvent convergence on the genuine paper clock. -/
local instance sameAmbientNaturalClockRescaleContinuousMeasurableCompletion20261011 {Space : Type*} [TopologicalSpace Space] : MeasurableSpace C(ℝ≥0, Space) := borel _
local instance sameAmbientNaturalClockRescaleContinuousBorelCompletion20261011 {Space : Type*} [TopologicalSpace Space] : BorelSpace C(ℝ≥0, Space) := ⟨rfl⟩
local instance sameAmbientNaturalClockRescaleCarrierMeasurableCompletion20261011 (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance sameAmbientNaturalClockRescaleCarrierBorelCompletion20261011 (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩
theorem ae_actual_natural_deterministic_common_ambient_same_limit
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∃ (edgeCoefficient vertexCoefficient : ℝ)
      (mass : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      0 < edgeCoefficient ∧ 0 < vertexCoefficient ∧
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < mass marks ∧ ∀ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks,
      ∀ compactness : CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))),
      letI := compactness
      letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundary)
        (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word) marks)),
      ∀ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩,
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1))))
        (boundary.map realization)) atTop (𝓝 0) →
      ∀ massProbability : IsProbabilityMeasure (boundary.map realization),
      ∀ massOpenPositive : (boundary.map realization).IsOpenPosMeasure,
      letI := massProbability
      letI := massOpenPositive
      ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
      ∀ anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩),
      ∀ data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization),
      ∀ initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth),
      ∀ (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times),
      ∀ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),

      Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩
        chemicalScale chemicalScalePositive times initial depth) atTop (𝓝 limitLaw) →

      ∀ (Ambient : Type*) [ambientMetric : MetricSpace Ambient] [ambientCompact : CompactSpace Ambient]
        [ambientMeasurable : MeasurableSpace Ambient] [ambientBorel : BorelSpace Ambient],
      ∀ sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth → Ambient,
      ∀ targetEmbedding : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ → Ambient,
      ∀ embeddingContinuous : Continuous targetEmbedding,
      (∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ point,
        dist (sources depth point) (targetEmbedding (actualStationaryElectricalVertex rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth point)) < tolerance) →
      ∀ countingSpeed : Bool,
        Tendsto (fun depth => actualPaperDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalScale chemicalScalePositive countingSpeed depth (initial depth) (sources depth)) atTop (𝓝 ((continuousCadlagProbabilityCompletion20261011 limitLaw
          (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))
          (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
          (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding embeddingContinuous).measurable.aemeasurable)) ∧
        Tendsto (fun depth => usualLocalJ1PathProbability (actualPaperDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalScale chemicalScalePositive countingSpeed depth (initial depth) (sources depth))) atTop
          (𝓝 (usualLocalJ1PathProbability ((continuousCadlagProbabilityCompletion20261011 limitLaw
          (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))
          (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
          (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 targetEmbedding embeddingContinuous).measurable.aemeasurable))) := by
  obtain ⟨edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, clockProperties⟩ :=
    ae_actual_paper_deterministic_NNReal_ratios_completion20261011 rule classicalRule p positive belowOne fixedPoint
      natural.growth (zero_lt_one.trans natural.aboveOne)
  refine ⟨edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, ?_⟩
  filter_upwards [clockProperties, ae_actual_natural_weighted_clock_rescale_same_limit
    rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative] with marks clocks rescaled
  refine ⟨clocks.1, ?_⟩
  intro typical compactness
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
  intro boundary probability atoms realization projection massProbability massOpenPositive
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  intro chemicalScale chemicalScalePositive anchor data initial times timeZero dense limitLaw observedWeak
  intro Ambient ambientMetric ambientCompact ambientMeasurable ambientBorel sources targetEmbedding embeddingContinuous placementClose countingSpeed
  letI := ambientMetric
  letI := ambientCompact
  letI := ambientMeasurable
  letI := ambientBorel
  have ratios := clocks.2 chemicalScale chemicalScalePositive countingSpeed
  have rescaledWeak := rescaled typical compactness boundary probability atoms realization projection massProbability massOpenPositive
    chemicalScale chemicalScalePositive anchor data initial times timeZero dense limitLaw observedWeak
    countingSpeed (actualPaperDeterministicClockRatioCompletion20261011 rule p natural.growth marks chemicalScale chemicalScalePositive countingSpeed)
    ratios.1 (Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) ratios.2.1 ratios.2.2
  have originalGlobalWeak : Tendsto (fun depth => actualPaperDeterministicGlobalLawCompletion20261011
      rule classicalRule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ chemicalScale chemicalScalePositive countingSpeed depth (initial depth)) atTop
      (𝓝 (limitLaw.map (continuousGlobalFamily_measurable_completion20261011
        (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))
        (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
        (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))).aemeasurable)) := by
    simpa only [actualPaperDeterministicGlobalLawCompletion20261011] using rescaledWeak
  have projectedCadlagWeak : Tendsto (fun depth => actualPaperDeterministicCadlagLawCompletion20261011
      rule classicalRule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ chemicalScale chemicalScalePositive countingSpeed depth (initial depth)) atTop
      (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw
        (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))
        (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
        (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time)))) := by
    apply probability_subtype_weak_of_val_weak_completion20261011
      (fun path : SkorokhodGlobalPathCompletion20261011 (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) => SkorokhodCadlagCompletion20261011 path)
    simp only [continuousCadlagProbability_val_completion20261011]
    convert originalGlobalWeak using 1
    funext depth
    exact actualPaperDeterministicCadlagLaw_val_completion20261011 rule classicalRule p positive belowOne fixedPoint
      natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
      chemicalScale chemicalScalePositive countingSpeed depth (initial depth)
  have placedWeak := actualPaperDeterministicPlacedCadlagLaw_tendsto rule classicalRule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
    chemicalScale chemicalScalePositive initial sources targetEmbedding embeddingContinuous placementClose countingSpeed _ projectedCadlagWeak
  exact ⟨placedWeak, integerJ1_weak_to_usualLocalJ1 _ _ placedWeak⟩

end
end IGSIII34.Diffusion

