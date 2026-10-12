import IGSIII34.Diffusion.ActualNaturalDiscreteClockRescaleCompletion
import IGSIII34.Diffusion.ActualPaperDiscreteDeterministicLawCompletion
import IGSIII34.Diffusion.ActualNaturalWeightedClockRescaleCompletion
import IGSIII34.Diffusion.ActualPaperDeterministicLawCompletion
import IGSIII34.Diffusion.ActualWeightedClockRescaleCompletion
import IGSIII34.Diffusion.ActualVertexSpeedGlobalWeakCompletion
import IGSIII34.Diffusion.ActualNaturalAdditiveClockCompletion
import IGSIII34.Diffusion.ActualDiscreteGlobalWholeWeakCompletion
import IGSIII34.Diffusion.ActualContinuousLimitAssemblyCompletion
import IGSIII34.Diffusion.ActualNaturalDegreeMassCompletion
import IGSIII34.Diffusion.ActualResolventUniformCompletion
import IGSIII34.Spectral.ActualNaturalSpectralWitnessCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII34.Spectral
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance rawNaturalPaperDiscreteDeterministicCompletionMeasurableCompletion {Carrier : Type*} [UniformSpace Carrier] : MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance rawNaturalPaperDiscreteDeterministicCompletionBorelCompletion {Carrier : Type*} [UniformSpace Carrier] : BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- The original natural field supplies all electrical convergence and mesh
inputs. Any actual Perron boundary realization with the same vertex ratios
therefore has whole finite-resolvent convergence on the genuine paper clock. -/
local instance rawNaturalPaperDiscreteDeterministicContinuousMeasurableCompletion {Space : Type*} [TopologicalSpace Space] : MeasurableSpace C(ℝ≥0, Space) := borel _
local instance rawNaturalPaperDiscreteDeterministicContinuousBorelCompletion {Space : Type*} [TopologicalSpace Space] : BorelSpace C(ℝ≥0, Space) := ⟨rfl⟩
local instance rawNaturalPaperDiscreteDeterministicCarrierMeasurableCompletion (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance rawNaturalPaperDiscreteDeterministicCarrierBorelCompletion (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩
theorem ae_actual_natural_paper_discrete_deterministic_cadlag_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
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
      ∀ data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization),
      ∀ initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth),
      ∀ (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times),
      ∀ initialLimit : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),
      Tendsto (fun depth => (initial depth).map
        (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth vertex)).aemeasurable)
        atTop (𝓝 initialLimit) →
      ∃ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),

        Tendsto (fun depth => actualPaperDiscreteDeterministicCadlagLawCompletion rule classicalRule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalScale chemicalScalePositive depth (initial depth)) atTop
          (𝓝 (continuousCadlagProbabilityCompletion limitLaw
            (fun path time => countableTimeContinuousSampleCompletion times dense path
              (Real.toNNReal (1 / (2 * (edgeCoefficient * mass marks))) * time))
            (fun path => (countableTimeContinuousSample_continuous_completion times dense path).comp (continuous_const.mul continuous_id))
            (fun time => countableTimeContinuousSample_evaluation_measurable_completion times dense
              (Real.toNNReal (1 / (2 * (edgeCoefficient * mass marks))) * time)))) := by
  obtain ⟨edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, clockLimits⟩ :=
    ae_actual_paper_deterministic_NNReal_ratios_completion rule classicalRule p positive belowOne fixedPoint natural.growth (zero_lt_one.trans natural.aboveOne)
  refine ⟨edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, ?_⟩
  filter_upwards [clockLimits, ae_actual_natural_discrete_clock_rescale_completion
    rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative] with marks clockProperties convergence
  refine ⟨clockProperties.1, ?_⟩
  intro typical compactness
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
    (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
  intro boundary probability atoms realization projection massProbability massOpenPositive
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  intro chemicalScale chemicalScalePositive anchor data initial times timeZero dense initialLimit initialConvergence
  obtain ⟨limitLaw, wholeWeak⟩ := convergence typical compactness boundary probability atoms realization projection
    massProbability massOpenPositive chemicalScale chemicalScalePositive anchor data initial times timeZero dense initialLimit initialConvergence
  refine ⟨limitLaw, ?_⟩
  have ratios := clockProperties.2 chemicalScale chemicalScalePositive false
  apply probability_subtype_weak_of_val_weak_completion
    (fun path : SkorokhodGlobalPathCompletion
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) => SkorokhodCadlagCompletion path)
  simp only [continuousCadlagProbability_val_completion]
  convert wholeWeak
    (actualPaperDeterministicClockRatioCompletion rule p natural.growth marks chemicalScale chemicalScalePositive false)
    (actualPaperDeterministicRatios_positive_of_classical_completion rule classicalRule p positive belowOne fixedPoint
      natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ chemicalScale chemicalScalePositive false)
    (Real.toNNReal (1 / (2 * (edgeCoefficient * mass marks)))) ratios.2.1 ratios.2.2 using 1
  funext depth
  exact actualPaperDiscreteDeterministicCadlagLaw_val_completion rule classicalRule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
    chemicalScale chemicalScalePositive depth (initial depth)
end
end IGSIII34.Diffusion


