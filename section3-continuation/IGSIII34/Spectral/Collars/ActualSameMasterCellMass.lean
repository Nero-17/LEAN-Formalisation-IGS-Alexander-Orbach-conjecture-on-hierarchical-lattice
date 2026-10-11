import IGSIII34.ResistanceLimit.ActualNaturalCommonChemicalPaperDiffusion
import IGSIII34.Spectral.Collars.ChemicalCellMass
import IGSIII34.Spectral.Collars.CarrierWordPoint
import IGSIII34.Spectral.Collars.PhysicalCellSelection
import IGSIII34.Spectral.Collars.PointMass

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open IGSIII34.Spectral IGSIII34.Diffusion
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance cellMass_ActualNaturalConstructedDiffusionWitnessLocal1 {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance cellMass_ActualNaturalConstructedDiffusionWitnessLocal2 {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance cellMass_actualNaturalConstructedDiffusionWitnessCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance cellMass_actualNaturalConstructedDiffusionWitnessCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance cellMass_ActualNaturalConstructedDiffusionWitnessCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance cellMass_ActualNaturalConstructedDiffusionWitnessCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance cellMass_ActualNaturalConstructedDiffusionWitnessCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance cellMass_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance cellMass_actualNaturalConstructedDiffusionWitnessCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (cellMass_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance cellMass_actualNaturalConstructedDiffusionWitnessTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (cellMass_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance cellMass_actualNaturalConstructedDiffusionWitnessInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance cellMass_actualNaturalConstructedDiffusionWitnessCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


variable (classicalRule : rule.Classical)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

local instance cellMass_exactChemicalCarrierMeasurable : MeasurableSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := borel _
local instance cellMass_exactChemicalCarrierBorel : BorelSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩

theorem exists_ae_actual_natural_common_chemical_cell_mass_and_paper_diffusion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∃ chemicalGrowth : ℝ, ∃ chemicalGrowthPositive : 0 < chemicalGrowth,
    ∃ amplitude : ℝ, ∃ amplitudeAtLeastOne : 1 ≤ amplitude, ∃ chemicalValue : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
    ∃ weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address, Tendsto (fun depth =>
          markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
            markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
          atTop (𝓝 (weight address marks))) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ fields : (∀ address, 0 < chemicalField rule p positive belowOne fixedPoint chemicalValue address marks ∧
        (edgePathFamily rule.network (marks (address,true))).shortest
          (fun edge => chemicalField rule p positive belowOne fixedPoint chemicalValue (address ++ [edge]) marks) =
          chemicalGrowth * chemicalField rule p positive belowOne fixedPoint chemicalValue address marks ∧
        Tendsto (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / chemicalGrowth ^ (depth + 1))
          atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint chemicalValue address marks))),
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
      letI : MeasurableSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) := borel _
      letI : BorelSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩
      (∀ depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth),
        homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩ depth vertex) =
        actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
          chemicalGrowth chemicalGrowthPositive
          (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
          lengthNonnegative lengthPositive childConvergence depth vertex) ∧
      NullSingletonClass (boundary.map realization) ∧
      (∀ depth,
        (∀ word : Fin (depth + 1) → (Fin rule.edges × Bool),
          (boundary.map (homeomorph.symm ∘ realization)) (actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
              chemicalGrowthPositive (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks typical.1.1.2.1
              (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
              (fun address => (fields address).1) (fun address => (fields address).2.2) depth word) =
            ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
        (∀ᵐ path ∂boundary, ∀ word : Fin (depth + 1) → (Fin rule.edges × Bool),
          homeomorph.symm (realization path) ∈ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
              chemicalGrowthPositive (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks typical.1.1.2.1
              (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
              (fun address => (fields address).1) (fun address => (fields address).2.2) depth word ↔ path (depth + 1) = word)) ∧
      (∀ depth, ∀ᵐ point ∂boundary.map (homeomorph.symm ∘ realization),
        ∃ label : Fin (depth + 1) → (Fin rule.edges × Bool), ∀ other,
          point ∈ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
              chemicalGrowthPositive (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks typical.1.1.2.1
              (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
              (fun address => (fields address).1) (fun address => (fields address).2.2) depth other ↔ other = label) ∧
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
  obtain ⟨chemicalGrowth, chemicalGrowthPositive, amplitude, amplitudeAtLeastOne, chemicalValue,
    weight, ratios, master⟩ := exists_ae_actual_natural_common_chemical_paper_diffusion
      rule classicalRule p positive belowOne fixedPoint natural
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks := by
    filter_upwards [ratios] with marks limits
    intro address
    exact ge_of_tendsto (limits address) (Eventually.of_forall (fun depth =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  obtain ⟨continuation⟩ := exists_actual_mass_continuation_completion20261011
    rule classicalRule p positive belowOne fixedPoint
  have atomless := actual_physical_mass_null_singletons rule classicalRule p positive belowOne fixedPoint
    natural continuation weight ratios nonnegative
  refine ⟨chemicalGrowth, chemicalGrowthPositive, amplitude, amplitudeAtLeastOne, chemicalValue,
    weight, ratios, ?_⟩
  filter_upwards [master, ratios, atomless] with marks model markRatios noAtoms
  rcases model with ⟨fields, eta, coefficient, start, etaPositive, etaBelowOne, coefficientNonnegative,
    radiusBounds, typical, compactness, boundary, realization, rootWeight, positiveWeights,
    probability, atoms, measurable, retained, convergence, projection, massProbability,
    massOpenPositive, support, lengthNonnegative, lengthPositive, childConvergence,
    homeomorph, inverseBirth, rest⟩
  letI := compactness
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  letI : MeasurableSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) := borel _
  letI : BorelSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩
  have electricAtomless := noAtoms typical compactness boundary probability atoms retained
    realization measurable convergence
  letI := electricAtomless
  have chemicalAtomless := inverse_homeomorph_boundary_mass_null_singletons
    homeomorph boundary realization measurable
  letI := chemicalAtomless
  have chemicalConvergence := actual_inverse_carrier_boundary_convergence rule classicalRule p positive belowOne
    fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
    ⟨marks,typical⟩ chemicalGrowth chemicalGrowthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
    lengthNonnegative lengthPositive childConvergence homeomorph inverseBirth boundary realization convergence
  have cellMass := actualChemicalWordComponent_mass_identification rule classicalRule p positive belowOne fixedPoint
    chemicalGrowth amplitude chemicalGrowthPositive (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks
    typical.1.1.2.1
    (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
    (fun address => (fields address).1) (fun address => (fields address).2.2)
    eta coefficient start etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
    (fun address => weight address marks) markRatios boundary atoms
    (homeomorph.symm ∘ realization) (homeomorph.symm.measurable.comp measurable) retained chemicalConvergence
  have uniqueCells : ∀ depth, ∀ᵐ point ∂boundary.map (homeomorph.symm ∘ realization),
      ∃ label : Fin (depth + 1) → (Fin rule.edges × Bool), ∀ other,
        point ∈ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
              chemicalGrowthPositive (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks typical.1.1.2.1
              (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
              (fun address => (fields address).1) (fun address => (fields address).2.2) depth other ↔ other = label := by
    intro depth
    apply pushforward_ae_unique_containing_cell boundary (homeomorph.symm ∘ realization)
      (homeomorph.symm.measurable.comp measurable) (fun path => path (depth + 1))
      (fun word => actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
              chemicalGrowthPositive (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks typical.1.1.2.1
              (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
              (fun address => (fields address).1) (fun address => (fields address).2.2) depth word)
      (fun word => (actualChemicalWordComponent_isClosed rule classicalRule p positive belowOne fixedPoint
        chemicalGrowth amplitude chemicalGrowthPositive (zero_lt_one.trans_le amplitudeAtLeastOne) chemicalValue marks
        typical.1.1.2.1
        (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
        (fun address => (fields address).1) (fun address => (fields address).2.2)
        eta coefficient start etaPositive.le etaBelowOne coefficientNonnegative radiusBounds depth word).measurableSet)
    exact (cellMass depth).2
  exact ⟨fields, eta, coefficient, start, etaPositive, etaBelowOne, coefficientNonnegative,
    radiusBounds, typical, compactness, boundary, realization, rootWeight, positiveWeights,
    probability, atoms, measurable, retained, convergence, projection, massProbability,
    massOpenPositive, support, lengthNonnegative, lengthPositive, childConvergence,
    homeomorph, inverseBirth, electricAtomless, cellMass, uniqueCells, rest⟩

end
end IGSIII34.ResistanceLimit
