import IGSIII34.Diffusion.ActualNaturalContinuousGlobalSkorokhodCompletion20261011
import IGSIII34.Diffusion.ActualContinuousCadlagWholeWeakCompletion20261011
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

local instance ActualNaturalContinuousCadlagCompletion20261011Local1 {Carrier : Type*} [UniformSpace Carrier] : MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance ActualNaturalContinuousCadlagCompletion20261011Local2 {Carrier : Type*} [UniformSpace Carrier] : BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- The original natural field supplies all electrical convergence and mesh
inputs. Any actual Perron boundary realization with the same vertex ratios
therefore has whole finite-resolvent convergence on the genuine paper clock. -/
local instance ActualNaturalContinuousCadlagCompletion20261011Local3 {Space : Type*} [TopologicalSpace Space] : MeasurableSpace C(ℝ≥0, Space) := borel _
local instance ActualNaturalContinuousCadlagCompletion20261011Local4 {Space : Type*} [TopologicalSpace Space] : BorelSpace C(ℝ≥0, Space) := ⟨rfl⟩
local instance ActualNaturalContinuousCadlagCompletion20261011Local5 (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance ActualNaturalContinuousCadlagCompletion20261011Local6 (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩
theorem ae_actual_natural_continuous_cadlag_completion20261011
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
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks,
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
      ∀ initialLimit : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),
      Tendsto (fun depth => (initial depth).map
        (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth vertex)).aemeasurable)
        atTop (𝓝 initialLimit) →
      ∃ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),

        Tendsto (fun depth => actualPaperContinuousElectricalCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalScale chemicalScalePositive initial depth) atTop
          (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense) (countableTimeContinuousSample_continuous_completion20261011 times dense) (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense))) := by
  filter_upwards [ae_actual_natural_continuous_global_skorokhod_completion20261011
    rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative] with marks convergence
  intro typical compactness
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
    (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
  intro boundary probability atoms realization projection massProbability massOpenPositive
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  intro chemicalScale chemicalScalePositive anchor data initial times timeZero dense initialLimit initialConvergence
  obtain ⟨limitLaw, weak⟩ := convergence typical compactness boundary probability atoms realization projection
    massProbability massOpenPositive chemicalScale chemicalScalePositive anchor data initial times timeZero dense initialLimit initialConvergence
  refine ⟨limitLaw, ?_⟩
  apply probability_subtype_weak_of_val_weak_completion20261011
    (fun path : SkorokhodGlobalPathCompletion20261011
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) => SkorokhodCadlagCompletion20261011 path)
  simp only [continuousCadlagProbability_val_completion20261011]
  convert weak using 1
  funext depth
  exact actualPaperContinuousElectricalCadlagLaw_val_completion20261011 rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
    chemicalScale chemicalScalePositive initial depth

end
end IGSIII34.Diffusion