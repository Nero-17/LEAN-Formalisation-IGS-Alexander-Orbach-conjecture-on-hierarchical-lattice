import IGSIII34.ResistanceLimit.ActualCommonChemicalPaperLaw
import IGSIII34.ResistanceLimit.ActualCommonChemicalContinuousPaperLaw
import IGSIII34.ResistanceLimit.ActualCommonChemicalVertexPaperLaw
import IGSIII34.Diffusion.ActualNaturalVertexSpeedGlobalCompletion20261011
import IGSIII34.Diffusion.UsualLocalJ1PathLaw
import IGSIII34.ResistanceLimit.ActualPaperCadlagSameLaw
import IGSIII34.ResistanceLimit.ActualPaperInitialLaw
import IGSIII34.ResistanceLimit.CommonChemicalDiracStarts
import IGSIII34.ResistanceLimit.ActualCommonChemicalStartingPoints
import IGSIII34.ResistanceLimit.ActualNaturalChemicalCarrier
import IGSIII34.Diffusion.ActualNaturalConstructedDiffusionWitness
import IGSIII34.Diffusion.ActualNaturalConstructedDiffusion
import IGSIII34.Diffusion.ActualNaturalContinuousGlobalSkorokhodCompletion20261011
import IGSIII34.Spectral.ActualNaturalTypicalSpectralCompletion20261011
import IGSIII34.Spectral.ActualSpectralDataCompletion20261011
import IGSIII34.Forms.ActualFormMassWitnessCompletion20261011
import IGSIII34.ResistanceLimit.ActualElectricalMassRetainedCompletion20261011
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion20261011

/-! The actual physical natural endpoint, Perron mass and spectral data
are assembled on one event of the original critical innovation law.
No compact carrier, mass measure or dense energy-domain hypothesis is
left to the caller. The same constructed continuous limit obeys the strong stopping-time kernel law and is the original walk path-law limit. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open IGSIII34.Spectral IGSIII34.Diffusion
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance ActualNaturalConstructedDiffusionWitnessLocal1 {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance ActualNaturalConstructedDiffusionWitnessLocal2 {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance actualNaturalConstructedDiffusionWitnessCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualNaturalConstructedDiffusionWitnessCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualNaturalConstructedDiffusionWitnessCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualNaturalConstructedDiffusionWitnessCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualNaturalConstructedDiffusionWitnessCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance actualNaturalConstructedDiffusionWitnessNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualNaturalConstructedDiffusionWitnessCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualNaturalConstructedDiffusionWitnessTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualNaturalConstructedDiffusionWitnessInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualNaturalConstructedDiffusionWitnessCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


theorem exists_ae_actual_natural_common_chemical_paper_diffusion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∃ chemicalGrowth : ℝ, ∃ chemicalGrowthPositive : 0 < chemicalGrowth,
    ∃ amplitude : ℝ, 1 ≤ amplitude ∧ ∃ chemicalValue : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
    ∃ weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address, Tendsto (fun depth =>
          markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
            markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
          atTop (𝓝 (weight address marks))) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (∀ address, 0 < chemicalField rule p positive belowOne fixedPoint chemicalValue address marks ∧
        (edgePathFamily rule.network (marks (address,true))).shortest
          (fun edge => chemicalField rule p positive belowOne fixedPoint chemicalValue (address ++ [edge]) marks) =
          chemicalGrowth * chemicalField rule p positive belowOne fixedPoint chemicalValue address marks ∧
        Tendsto (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / chemicalGrowth ^ (depth + 1))
          atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint chemicalValue address marks))) ∧
      ∃ chemicalEta chemicalCoefficient : ℝ, ∃ chemicalStart : ℕ,
      ∃ chemicalEtaPositive : 0 < chemicalEta, ∃ chemicalEtaBelowOne : chemicalEta < 1,
      ∃ chemicalCoefficientNonnegative : 0 ≤ chemicalCoefficient,
      ∃ chemicalRadiusBounds : ∀ address opened depth, chemicalStart ≤ address.length →
        (markedTerminalComponentRadius rule marks depth address opened : ℝ) / chemicalGrowth ^ (depth + 1 + address.length) ≤
          chemicalCoefficient * chemicalEta ^ address.length,
      ∃ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks,
      ∃ compactness : CompactSpace (UniformSpace.Completion
        (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))),
      letI := compactness
      letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
      ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
      ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
        ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩,
      weight [] marks = 1 ∧
      (∀ address, 0 ≤ weight address marks ∧
        (retainedComponentState rule marks address = .connected → 0 < weight address marks)) ∧
      IsProbabilityMeasure boundary ∧
      (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
      Measurable realization ∧
      (∀ᵐ path ∂boundary, ∀ depth,
        Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive) ∧
      (∀ᵐ path ∂boundary, Tendsto (fun depth => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1)))
          atTop (𝓝 (realization path))) ∧
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1))))
        (boundary.map realization)) atTop (𝓝 0) ∧
      ∃ massProbability : IsProbabilityMeasure (boundary.map realization),
      ∃ massOpenPositive : (boundary.map realization).IsOpenPosMeasure,
      letI := massProbability
      letI := massOpenPositive
      (boundary.map realization).support = Set.univ ∧
      ∃ lengthNonnegative : ∀ depth edge, 0 ≤ chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks depth edge,
      ∃ lengthPositive : ∀ depth edge, stationaryConfiguration rule marks depth edge = true →
        0 < chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks depth edge,
      ∃ childConvergence : ∀ coarse edge, Tendsto (fun fine =>
        (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
          (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
          chemicalGrowth ^ (coarse + fine + 2)) atTop
        (𝓝 (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks coarse edge)),
      ∃ homeomorph : (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) ≃ₜ (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩),
      (∀ depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth),
        homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩ depth vertex) =
        actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
          chemicalGrowth chemicalGrowthPositive
          (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
          lengthNonnegative lengthPositive childConvergence depth vertex) ∧
      ∃ Ambient : Type, ∃ ambientMetric : MetricSpace Ambient,
      letI := ambientMetric
      ∃ complete : CompleteSpace Ambient, ∃ compact : CompactSpace Ambient,
      letI := complete
      letI := compact
      ∃ target : (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) → Ambient,
      ∃ targetIsometry : Isometry target,
      ∃ sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks)
        chemicalGrowth chemicalGrowthPositive depth → Ambient,
      (∀ depth, Isometry (sources depth)) ∧
      (∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
        dist (sources depth vertex) (target (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
          chemicalGrowth chemicalGrowthPositive
          (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
          lengthNonnegative lengthPositive childConvergence depth vertex)) < tolerance) ∧
      (∀ vertices : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth,
        ∀ point : actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
          (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
          lengthNonnegative lengthPositive childConvergence,
        Tendsto (fun depth => sources depth (vertices depth)) atTop (𝓝 (target point)) →
        Tendsto (fun depth => (diracProba (vertices depth)).map
          (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth =>
            actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
              (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩ depth vertex)).aemeasurable)
          atTop (𝓝 (diracProba (homeomorph point)))) ∧
      letI : MeasurableSpace Ambient := borel Ambient
      letI : BorelSpace Ambient := ⟨rfl⟩
      (      ∀ anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩),
      ∃ data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization),
      ∀ initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth),
      ∀ (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times),
      ∀ initialLimit : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),
      Tendsto (fun depth => (initial depth).map
        (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth vertex)).aemeasurable)
        atTop (𝓝 initialLimit) →
    ∃ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),
      Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011
        rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩
        chemicalGrowth chemicalGrowthPositive times initial depth) atTop (𝓝 limitLaw) ∧
      (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩)).map
        (fun path => countableTimeContinuousSampleCompletion20261011 times dense path 0) = (initialLimit : Measure _) ∧
      (∀ᵐ sample ∂(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)), countableTimeLocalUniformContinuityCompletion20261011 times sample) ∧
      (∀ sample : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩, Continuous (countableTimeContinuousSampleCompletion20261011 times dense sample)) ∧
      Tendsto (fun depth => actualPaperContinuousElectricalGlobalJ1LawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ chemicalGrowth chemicalGrowthPositive initial depth) atTop
        (𝓝 (limitLaw.map (countableSkorokhodGlobalSample_measurable_completion20261011 times dense).aemeasurable)) ∧
      Tendsto (fun depth => actualPaperDiscreteElectricalCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive initial depth) atTop
        (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense))) ∧
      Tendsto (fun depth => actualPaperPlacedDiscreteCadlagLaw rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive initial sources depth) atTop
        (𝓝 ((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable)) ∧
      Tendsto (fun depth => actualPaperPlacedContinuousCadlagLaw rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive initial sources depth) atTop
        (𝓝 ((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable)) ∧
      Tendsto (fun depth => actualVertexVariableSpeedPlacedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive depth (initial depth) (sources depth)) atTop
        (𝓝 ((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable)) ∧
      Tendsto (fun depth => usualLocalJ1PathProbability (actualPaperPlacedDiscreteCadlagLaw rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive initial sources depth)) atTop
        (𝓝 (usualLocalJ1PathProbability ((continuousCadlagProbabilityCompletion20261011 limitLaw
          (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable))) ∧
      Tendsto (fun depth => usualLocalJ1PathProbability (actualPaperPlacedContinuousCadlagLaw rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive initial sources depth)) atTop
        (𝓝 (usualLocalJ1PathProbability ((continuousCadlagProbabilityCompletion20261011 limitLaw
          (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable))) ∧
      Tendsto (fun depth => usualLocalJ1PathProbability (actualVertexVariableSpeedPlacedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive depth (initial depth) (sources depth))) atTop
        (𝓝 (usualLocalJ1PathProbability ((continuousCadlagProbabilityCompletion20261011 limitLaw
          (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable))) ∧
      ∀ (time : (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) → WithTop ℝ≥0),
      ∀ stopping : IsStoppingTime
        (Filtration.natural (fun present (path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) => countableTimeContinuousSampleCompletion20261011 times dense path present)
          (fun present => (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense present).stronglyMeasurable)) time,
      (∀ᵐ path ∂(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)), time path ≠ ⊤) → ∀ future : ℝ≥0,
      ∀ event : Set (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),
      MeasurableSet[stopping.measurableSpace] event →
      ((limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)).restrict event).map
        (fun path => countableTimeContinuousSampleCompletion20261011 times dense path ((time path).untopA + future)) =
        (actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization) data future) ∘ₘ
        (((limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)).restrict event).map
          (fun path => countableTimeContinuousSampleCompletion20261011 times dense path (time path).untopA))) ∧

      ∀ anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩),
      ∃ data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
        anchor (boundary.map realization),
      ∀ᵐ point ∂boundary.map realization,
        Tendsto (fun time => -2 * Real.log (actualSpectralHeatKernelCompletion20261011
          rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization) data time point point) / Real.log time)
          (𝓝[>] 0) (𝓝 (2 * Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
            Real.log (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth))) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion20261011 rule classicalRule p positive belowOne fixedPoint natural
  have growthPositive := zero_lt_one.trans natural.aboveOne
  let electricalEta : ℝ := (natural.growth + 1) / (2 * natural.growth)
  have electricalEtaPositive : 0 < electricalEta := div_pos (by linarith) (by positivity)
  have electricalEtaBelowOne : electricalEta < 1 := (div_lt_one (by positivity : 0 < 2 * natural.growth)).mpr (by linarith [natural.aboveOne])
  have electricalProduct : 1 < natural.growth * electricalEta := by
    have identity : natural.growth * electricalEta = (natural.growth + 1) / 2 := by dsimp [electricalEta]; field_simp
    rw [identity]
    linarith [natural.aboveOne]
  obtain ⟨chemicalConstant, chemicalGrowth, _, _, chemicalLower, _, chemicalMeanBounds,
    chemicalValue, _, _, _, amplitude, amplitudeLower, chemicalFields, _, _, _, _⟩ :=
    exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  have chemicalAboveOne : 1 < chemicalGrowth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le chemicalLower
  have chemicalGrowthPositive := zero_lt_one.trans chemicalAboveOne
  let chemicalEta : ℝ := (chemicalGrowth + 1) / (2 * chemicalGrowth)
  have chemicalEtaPositive : 0 < chemicalEta := div_pos (by linarith) (by positivity)
  have chemicalEtaBelowOne : chemicalEta < 1 := (div_lt_one (by positivity : 0 < 2 * chemicalGrowth)).mpr (by linarith)
  have chemicalProduct : 1 < chemicalGrowth * chemicalEta := by
    have identity : chemicalGrowth * chemicalEta = (chemicalGrowth + 1) / 2 := by dsimp [chemicalEta]; field_simp
    rw [identity]
    linarith
  obtain ⟨weight, ratios, witnesses⟩ := exists_ae_actual_natural_constructed_diffusion_spectral_witness
    rule classicalRule p positive belowOne fixedPoint natural
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address, 0 ≤ weight address marks := by
    filter_upwards [witnesses] with marks witness
    obtain ⟨typical, compactness, boundary, realization, _, positiveWeights, _⟩ := witness
    exact fun address => (positiveWeights address).1
  refine ⟨chemicalGrowth, chemicalGrowthPositive, amplitude, amplitudeLower, chemicalValue, weight, ratios, ?_⟩
  filter_upwards [witnesses,
    stationaryCarrierTypical_ae_fixed_cluster rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      classicalRule constant constantPositive natural.aboveOne growthBounds fixed membership electricalEta electricalEtaPositive electricalEtaBelowOne electricalProduct,
    chemicalFields,
    actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint chemicalConstant chemicalGrowth
      chemicalGrowthPositive chemicalMeanBounds chemicalEta chemicalEtaPositive chemicalEtaBelowOne chemicalProduct,
    ae_actual_natural_degree_mass_tendsto_completion20261011 rule classicalRule p positive belowOne fixedPoint natural weight ratios nonnegative,
    ae_actual_natural_additive_clock_prefix_probability_tendsto_completion20261011 rule classicalRule p positive belowOne fixedPoint natural weight ratios nonnegative,
    ae_actualCountingClock_density_bound_completion20261011 rule classicalRule p positive belowOne fixedPoint]
    with marks witness carrier fields chemicalMesh degrees clockPrefix clockDensity
  obtain ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability, atoms,
    measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support, paths, spectra⟩ := witness
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
    growthPositive ⟨marks,typical.1.1⟩) := compactness
  letI := massProbability
  letI := massOpenPositive
  obtain ⟨lengthNonnegative, lengthPositive, childConvergence⟩ := actual_block_lengths_of_terminal_field
    rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalGrowthPositive (zero_lt_one.trans_le amplitudeLower)
    chemicalValue marks typical.1.1.2.1 (fun address => (fields address).1) (fun address => (fields address).2.2)
  obtain ⟨chemicalStart, chemicalBounds⟩ := chemicalMesh
  obtain ⟨electricalStart, electricalBounds⟩ := carrier.2.2.2
  let homeomorph := actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
    lengthNonnegative lengthPositive childConvergence carrier.2.1 carrier.2.2.1
    electricalEta ((rule.edges + 1 : ℝ) / (1 - electricalEta)) electricalStart electricalEtaPositive.le electricalEtaBelowOne electricalBounds
    chemicalEta ((rule.edges + 1 : ℝ) / (1 - chemicalEta)) chemicalStart chemicalEtaPositive.le chemicalEtaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr chemicalEtaBelowOne).le) chemicalBounds
  have birthIdentity (depth : ℕ) (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth) :=
    actualChemicalElectricalCarrierHomeomorph_symm_birth_completion20261011 rule p positive belowOne fixedPoint
      natural.growth (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
      lengthNonnegative lengthPositive childConvergence carrier.2.1 carrier.2.2.1
      electricalEta ((rule.edges + 1 : ℝ) / (1 - electricalEta)) electricalStart electricalEtaPositive.le electricalEtaBelowOne electricalBounds
      chemicalEta ((rule.edges + 1 : ℝ) / (1 - chemicalEta)) chemicalStart chemicalEtaPositive.le chemicalEtaBelowOne
      (div_nonneg (by positivity) (sub_pos.mpr chemicalEtaBelowOne).le) chemicalBounds depth vertex
  obtain ⟨Ambient, ambientMetric, complete, compact, target, targetIsometry, sources, sourceIsometries, placementClose⟩ :=
    exists_actual_chemical_common_isometric_realisation_completion20261011 rule classicalRule marks typical.1.1.2.1
      (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
      chemicalGrowth chemicalGrowthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
      lengthNonnegative lengthPositive childConvergence chemicalEta ((rule.edges + 1 : ℝ) / (1 - chemicalEta)) chemicalStart
      chemicalEtaPositive.le chemicalEtaBelowOne (div_nonneg (by positivity) (sub_pos.mpr chemicalEtaBelowOne).le) chemicalBounds
  letI := ambientMetric
  letI := complete
  letI := compact
  letI : MeasurableSpace Ambient := borel Ambient
  letI : BorelSpace Ambient := ⟨rfl⟩
  have startingPoints : ∀ vertices : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth,
      ∀ point, Tendsto (fun depth => sources depth (vertices depth)) atTop (𝓝 (target point)) →
      Tendsto (fun depth => (diracProba (vertices depth)).map
        (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            growthPositive ⟨marks,typical.1.1⟩ depth vertex)).aemeasurable)
        atTop (𝓝 (diracProba (homeomorph point))) := by
    intro vertices point startingConvergence
    exact actual_common_chemical_dirac_starting_laws_tendsto rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
      lengthNonnegative lengthPositive childConvergence homeomorph birthIdentity target targetIsometry sources placementClose
      vertices point startingConvergence
  refine ⟨fields, chemicalEta, ((rule.edges + 1 : ℝ) / (1 - chemicalEta)), chemicalStart,
    chemicalEtaPositive, chemicalEtaBelowOne, (div_nonneg (by positivity) (sub_pos.mpr chemicalEtaBelowOne).le), chemicalBounds,
    typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability, atoms,
    measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support,
    lengthNonnegative, lengthPositive, childConvergence, homeomorph, birthIdentity, Ambient, ambientMetric, complete, compact,
    target, targetIsometry, sources, sourceIsometries, placementClose, startingPoints, ?_, spectra⟩
  intro anchor
  obtain ⟨data, _⟩ := spectra anchor
  refine ⟨data, ?_⟩
  intro initial times timeZero dense initialLimit initialConvergence
  obtain ⟨limitLaw, weak, regular, continuous, continuousWeak, stopping⟩ :=
    paths chemicalGrowth chemicalGrowthPositive anchor data initial times timeZero dense initialLimit initialConvergence
  let measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical.1.1⟩) := ⟨boundary.map realization, massProbability⟩
  letI : (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical.1.1⟩)).IsOpenPosMeasure := massOpenPositive
  have degreeLimit := degrees typical.1.1 boundary boundaryProbability atoms realization projections chemicalGrowth chemicalGrowthPositive
  have globalWeak := actual_discrete_global_skorokhod_convergence_completion20261011 rule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive measure anchor
    (Nat.zero_lt_of_lt classicalRule.edges_gt_one) natural.aboveOne degreeLimit carrier.2.1 carrier.2.2.1
    electricalEta ((rule.edges + 1 : ℝ) / (1 - electricalEta)) electricalStart electricalEtaPositive.le electricalEtaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr electricalEtaBelowOne).le) electricalBounds times dense initial limitLaw id tendsto_id weak
  have cadlagWeak : Tendsto (fun depth => actualPaperDiscreteElectricalCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
      natural.growth (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive initial depth) atTop
      (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
        (countableTimeContinuousSample_continuous_completion20261011 times dense)
        (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense))) := by
    apply actual_paper_discrete_cadlag_same_law rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive
      initial times dense limitLaw
    simpa only [actualPaperDiscreteElectricalGlobalJ1LawCompletion20261011, id_eq] using globalWeak
  have continuousCadlagWeak := actual_paper_continuous_cadlag_same_law rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive
    initial times dense limitLaw continuousWeak
  obtain ⟨clockBound, clockBoundPositive, clockBounded⟩ := clockDensity chemicalGrowth chemicalGrowthPositive
  have vertexGlobalWeak := actual_vertex_speed_global_weak_of_clock_completion20261011 rule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive measure anchor
    (Nat.zero_lt_of_lt classicalRule.edges_gt_one) natural.aboveOne degreeLimit carrier.2.1 carrier.2.2.1
    electricalEta ((rule.edges + 1 : ℝ) / (1 - electricalEta)) electricalStart electricalEtaPositive.le electricalEtaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr electricalEtaBelowOne).le) electricalBounds initial clockBound clockBoundPositive.le
    (fun depth vertex => (clockBounded depth vertex).1.2)
    (clockPrefix typical compactness boundary boundaryProbability atoms realization projections massProbability massOpenPositive
      chemicalGrowth chemicalGrowthPositive initial)
    (limitLaw.map (continuousGlobalFamily_measurable_completion20261011
      (countableTimeContinuousSampleCompletion20261011 times dense)
      (countableTimeContinuousSample_continuous_completion20261011 times dense)
      (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).aemeasurable)
    (by simpa only [actualPaperDiscreteElectricalGlobalJ1LawCompletion20261011, id_eq] using globalWeak)
  have vertexCadlagWeak := actual_vertex_cadlag_same_law rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive
    initial times dense limitLaw vertexGlobalWeak
  have initialLaw := actual_paper_limit_initial_law rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive
    initial times timeZero dense initialLimit initialConvergence limitLaw weak regular
  have actualPlacementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (sources depth vertex) ((target ∘ homeomorph.symm) (actualStationaryElectricalVertex rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) growthPositive ⟨marks,typical.1.1⟩ depth vertex)) < tolerance := by
    intro tolerance tolerancePositive
    filter_upwards [placementClose tolerance tolerancePositive] with depth close
    intro vertex
    change dist (sources depth vertex) (target (homeomorph.symm
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) growthPositive ⟨marks,typical.1.1⟩ depth vertex))) < tolerance
    rw [birthIdentity depth vertex]
    exact close vertex
  have placedDiscreteWeak := actualPaperPlacedDiscreteCadlagLaw_tendsto rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive initial sources
    (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous) actualPlacementClose _ cadlagWeak
  have placedContinuousWeak := actualPaperPlacedContinuousCadlagLaw_tendsto rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive initial sources
    (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous) actualPlacementClose _ continuousCadlagWeak
  have placedVertexWeak := actualVertexPlacedCadlagLaw_tendsto rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive initial sources
    (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous) actualPlacementClose _ vertexCadlagWeak
  refine ⟨limitLaw, weak, initialLaw, regular, continuous, continuousWeak, cadlagWeak,
    placedDiscreteWeak, placedContinuousWeak, placedVertexWeak, ?_, ?_, ?_, stopping⟩
  · exact integerJ1_weak_to_usualLocalJ1 _ _ placedDiscreteWeak
  · exact integerJ1_weak_to_usualLocalJ1 _ _ placedContinuousWeak
  · exact integerJ1_weak_to_usualLocalJ1 _ _ placedVertexWeak

end
end IGSIII34.ResistanceLimit
