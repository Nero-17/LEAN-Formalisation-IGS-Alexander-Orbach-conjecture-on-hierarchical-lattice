import IGSIII34.Spectral.Collars.ActualSameMasterAllClocks
import IGSIII34.ResistanceLimit.ActualSameCarrierMeasuredMarkedState
import IGSIII34.Diffusion.OriginalJointCommonAmbientWeak
import IGSIII34.Diffusion.OriginalJointContinuousSampleLaw
import IGSIII34.Spectral.Collars.ActualFiniteOriginalJointResponseTransport
import IGSIII34.Spectral.Collars.ActualFiniteOriginalJointStatePlacement
import IGSIII34.Diffusion.WholeCadlagProbabilityTransport
import IGSIII34.Spectral.Collars.ActualAnnealedStartingConvergence
import IGSIII34.Spectral.Collars.ActualFiniteOriginalJointKernel
import IGSIII34.Spectral.Collars.ActualFiniteAnnealedNaturalPlacedLaw
import IGSIII34.ResistanceLimit.ActualNaturalCommonChemicalPaperDiffusion
import IGSIII34.Spectral.Collars.ChemicalCellMass
import IGSIII34.Spectral.Collars.CarrierWordPoint
import IGSIII34.Spectral.Collars.PhysicalCellSelection
import IGSIII34.Spectral.Collars.PointMass
import IGSIII34.Spectral.Collars.SameCarrierMarkedGHP
import IGSIII34.Spectral.Collars.CarrierPlacedMass
import IGSIII34.Spectral.Collars.PhysicalComponentLogMass
import IGSIII34.ResistanceLimit.ActualNaturalRawElectricalMarkedGHP
import IGSIII34.Spectral.Collars.AllDeterministicSameAmbient

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open IGSIII34.Spectral IGSIII34.Diffusion
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance sectionThreeOriginalJointExistence_ActualNaturalConstructedDiffusionWitnessLocal1 {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance sectionThreeOriginalJointExistence_ActualNaturalConstructedDiffusionWitnessLocal2 {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance sectionThreeOriginalJointExistence_ActualNaturalConstructedDiffusionWitnessCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance sectionThreeOriginalJointExistence_ActualNaturalConstructedDiffusionWitnessCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance sectionThreeOriginalJointExistence_ActualNaturalConstructedDiffusionWitnessCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance sectionThreeOriginalJointExistence_actualNaturalConstructedDiffusionWitnessCompleteCompletion20261011 : CompleteSpace
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

local instance sectionThreeOriginalJointExistence_exactChemicalCarrierMeasurable : MeasurableSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := borel _
local instance sectionThreeOriginalJointExistence_exactChemicalCarrierBorel : BorelSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩


theorem exists_ae_actual_natural_original_joint_limit
    (classicalRule : rule.Classical)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times) :
    ∃ chemicalGrowth : ℝ, ∃ chemicalGrowthPositive : 0 < chemicalGrowth,
      ∀ initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
          Fin (rule.generation depth).vertices,
      (∀ depth, Measurable (initial depth)) →
      ActualAnnealedStartingConvergence rule p positive belowOne fixedPoint natural initial →
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∃ law : ProbabilityMeasure OriginalJointCompactSpace,
          OriginalJointUsualTestRegular law ∧
          ∀ kind : Fin 3, Tendsto (fun depth => actualFiniteOriginalJointResponse rule chemicalGrowth
            chemicalGrowthPositive depth
            (fun cfg => (actualFiniteAnnealedNaturalClock rule chemicalGrowth chemicalGrowthPositive depth natural.growth kind cfg : ℝ)) kind
            (markedGenerationConfiguration rule marks depth [] true, initial depth marks)) atTop (𝓝 law) := by
  have frozenMaster := exists_ae_actual_natural_common_section_three_all_clocks
    rule classicalRule p positive belowOne fixedPoint natural
  rcases frozenMaster with ⟨chemicalGrowth, chemicalGrowthPositive, amplitude, amplitudeAtLeastOne, chemicalValue,
    weight, ratios, edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, models⟩
  refine ⟨chemicalGrowth, chemicalGrowthPositive, ?_⟩
  intro initial initialMeasurable starting
  filter_upwards [models, starting] with marks model startConvergence
  rcases model with ⟨massPositive, fields, eta, coefficient, start, etaPositive, etaBelowOne,
    coefficientNonnegative, radiusBounds, typical, compactness, model⟩
  letI := compactness
  rcases model with ⟨boundary, realization, rootWeight, positiveWeights, probability, model⟩
  letI := probability
  rcases model with ⟨atoms, measurable, retained, convergence, projection, massProbability,
    massOpenPositive, model⟩
  letI := massProbability
  letI := massOpenPositive
  rcases model with ⟨support, lengthNonnegative, lengthPositive, childConvergence, homeomorph, model⟩
  rcases model with ⟨inverseBirth, electricAtomless, cellMass, uniqueCells, physicalLog, markedGHP,
    rawMarked, Ambient, ambientMetric, complete, compact, target, targetIsometry, sources,
    sourcesIsometry, placementClose, diracCompatibility, countingPlaced, degreePlaced, processes, spectral⟩
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩) := compactness
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  letI := ambientMetric
  letI := complete
  letI := compact
  letI : MeasurableSpace Ambient := borel Ambient
  letI : BorelSpace Ambient := ⟨rfl⟩
  letI : MeasurableSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) := borel _
  letI : BorelSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩
  letI : CompactSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩ classicalRule chemicalGrowth chemicalGrowthPositive
        (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
        lengthNonnegative lengthPositive childConvergence) := homeomorph.symm.compactSpace
  let states : ℕ → JointMeasuredMarkedState Ambient := fun depth =>
        (continuousNonemptyCompactRange (sources depth) (sourcesIsometry depth).continuous,
          fun side => sources depth (actualFiniteClusterTerminal rule (stationaryConfiguration rule marks)
            (fun depth => markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true)
            chemicalGrowth chemicalGrowthPositive depth side),
          fun counting => (actualBothFiniteClusterProbability rule (stationaryConfiguration rule marks)
            (fun depth => markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true)
            chemicalGrowth chemicalGrowthPositive depth counting).map (measurable_of_finite (sources depth)).aemeasurable)
  let state : JointMeasuredMarkedState Ambient :=
        (continuousNonemptyCompactRange target targetIsometry.continuous,
          fun side => target (actualChemicalTerminal rule classicalRule (stationaryConfiguration rule marks)
            (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
            (fun depth => markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true)
            chemicalGrowth chemicalGrowthPositive
            (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
            lengthNonnegative lengthPositive childConvergence side),
          fun _ => ProbabilityMeasure.map (⟨boundary.map realization, massProbability⟩ : ProbabilityMeasure
            (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
              (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩))
            (targetIsometry.continuous.comp homeomorph.symm.continuous).measurable.aemeasurable)
  have imagesConverge := actual_common_chemical_compact_images_tendsto rule classicalRule marks
    (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
    chemicalGrowth chemicalGrowthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
    lengthNonnegative lengthPositive childConvergence target targetIsometry sources sourcesIsometry placementClose
    eta coefficient start etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
  have marksConverge := fun side => actual_common_chemical_terminal_tendsto rule classicalRule marks typical.1.1.2.1
    (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
    chemicalGrowth chemicalGrowthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
    lengthNonnegative lengthPositive childConvergence target sources placementClose side
  have massConverge (counting : Bool) : Tendsto (fun depth => levyProkhorovEDist
      ((states depth).2.2 counting : Measure Ambient) (state.2.2 counting : Measure Ambient)) atTop (𝓝 0) := by
    cases counting
    · exact degreePlaced.2
    · exact countingPlaced.2
  have spatial := jointMeasuredMarkedStateCost_tendsto_zero states state imagesConverge marksConverge massConverge
  obtain ⟨point, pointConvergence⟩ := startConvergence typical
  let selected : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth :=
    fun depth => actualAnnealedSelectedVertex rule marks depth (initial depth marks)
  let initialProb := fun depth => diracProba (X := ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth) (selected depth)
  have initialWeak := actualAnnealedSelectedVertex_initial_probability_tendsto rule p positive belowOne fixedPoint natural marks typical
    (fun depth => initial depth marks) chemicalGrowth chemicalGrowthPositive point pointConvergence
  let anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne)
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical⟩) :=
    ⟦⟨0, selected 0⟩⟧
  have processWitness := processes anchor
  rcases processWitness with ⟨data, process⟩
  have limitWitness := process initialProb times timeZero dense (diracProba point) initialWeak
  rcases limitWitness with ⟨limitLaw, observedWeak, deterministic, remaining⟩
  rcases remaining with ⟨initialLaw, regular, continuous, continuousWeak, cadlagWeak,
    placedDiscreteWeak, placedContinuousWeak, placedVertexWeak, rest⟩
  let targetMarks := fun side => actualChemicalTerminal rule classicalRule (stationaryConfiguration rule marks)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks,typical.1.1⟩)
    (fun depth => markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true)
    chemicalGrowth chemicalGrowthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks)
    lengthNonnegative lengthPositive childConvergence side
  let targetMasses := fun _ : Bool =>
    ProbabilityMeasure.map (⟨boundary.map realization, massProbability⟩ : ProbabilityMeasure
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩)) homeomorph.symm.continuous.measurable.aemeasurable
  let electricalLaw := continuousCadlagProbabilityCompletion20261011 limitLaw
    (countableTimeContinuousSampleCompletion20261011 times dense)
    (countableTimeContinuousSample_continuous_completion20261011 times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)
  let targetLaw := electricalLaw.map
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 homeomorph.symm homeomorph.symm.continuous).measurable.aemeasurable
  let crossing := fun depth => markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true
  let clockPositive := fun depth kind => actualFiniteAnnealedNaturalClock_positive rule (stationaryConfiguration rule marks)
    chemicalGrowth chemicalGrowthPositive depth (crossing depth) natural.growth (zero_lt_one.trans natural.aboveOne) kind
  let sourceMarks := fun depth => actualFullConfigurationMark rule (stationaryConfiguration rule marks)
    chemicalGrowth chemicalGrowthPositive depth (crossing depth)
  let sourceMasses := fun depth => actualFullConfigurationMass rule (stationaryConfiguration rule marks)
    chemicalGrowth chemicalGrowthPositive depth (crossing depth)
  let sourceLaws := fun kind depth => actualFullConfigurationPathLaw rule (stationaryConfiguration rule marks)
    chemicalGrowth chemicalGrowthPositive depth (crossing depth) (selected depth).val
    (actualFiniteAnnealedNaturalClock rule chemicalGrowth chemicalGrowthPositive depth natural.growth kind (stationaryConfiguration rule marks depth))
    (clockPositive depth kind) kind
  have sourceStateIdentity (depth : ℕ) :
      jointMeasuredMarkedStateMap (sources depth) (sourcesIsometry depth).continuous
        (originalJointCompactFullState (sourceMarks depth) (sourceMasses depth)) = states depth := by
    exact actualFullConfigurationFullState_placed rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive
      depth crossing (sources depth) (sourcesIsometry depth).continuous
  letI := Nonempty.intro (targetMarks true)
  have targetStateIdentity : jointMeasuredMarkedStateMap target targetIsometry.continuous
      (originalJointCompactFullState targetMarks targetMasses) = state := by
    rw [jointMeasuredMarkedStateMap_fullState_range]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext side
        apply ProbabilityMeasure.toMeasure_injective
        exact Measure.map_map targetIsometry.continuous.measurable homeomorph.symm.continuous.measurable
  have spatialOriginal : Tendsto (fun depth => jointMeasuredMarkedStateCost
      (jointMeasuredMarkedStateMap (sources depth) (sourcesIsometry depth).continuous
        (originalJointCompactFullState (sourceMarks depth) (sourceMasses depth)))
      (jointMeasuredMarkedStateMap target targetIsometry.continuous
        (originalJointCompactFullState targetMarks targetMasses))) atTop (𝓝 0) := by
    simpa only [sourceStateIdentity, targetStateIdentity] using spatial
  have paths (kind : Fin 3) : Tendsto (fun depth => (sourceLaws kind depth).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (sources depth) (sourcesIsometry depth).continuous).measurable.aemeasurable) atTop
      (𝓝 (targetLaw.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        target targetIsometry.continuous).measurable.aemeasurable)) := by
    fin_cases kind
    · simp only [sourceLaws, targetLaw, electricalLaw, actualFullConfigurationPathLaw_placed,
        skorokhodCadlagProbabilityMap_comp]
      convert placedDiscreteWeak using 1
      funext depth
      exact actualFiniteAnnealedNaturalPlacedLaw_discrete rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive selected sources depth
    · simp only [sourceLaws, targetLaw, electricalLaw, actualFullConfigurationPathLaw_placed,
        skorokhodCadlagProbabilityMap_comp]
      convert placedContinuousWeak using 1
      funext depth
      exact actualFiniteAnnealedNaturalPlacedLaw_rate_one rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive selected sources depth
    · simp only [sourceLaws, targetLaw, electricalLaw, actualFullConfigurationPathLaw_placed,
        skorokhodCadlagProbabilityMap_comp]
      convert placedVertexWeak using 1
      funext depth
      exact actualFiniteAnnealedNaturalPlacedLaw_inverse_degree rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive selected sources depth
  refine ⟨originalJointCompactPathLaw targetMarks targetMasses targetLaw, ?_, ?_⟩
  · exact originalJointCompactPathLaw_spatial_continuousSample_regular targetMarks targetMasses limitLaw
      (countableTimeContinuousSampleCompletion20261011 times dense)
      (countableTimeContinuousSample_continuous_completion20261011 times dense)
      (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)
      homeomorph.symm homeomorph.symm.continuous
  · intro kind
    have weak := originalJointCompactPathLaws_weak_of_isometric_common_ambient
      (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth)
      sourceMarks sourceMasses targetMarks targetMasses (sourceLaws kind) targetLaw
      sources sourcesIsometry target targetIsometry spatialOriginal (paths kind)
    convert weak using 1
    funext depth
    rw [← actualFiniteOriginalJointResponse_configuration_transport rule (stationaryConfiguration rule marks)
      chemicalGrowth chemicalGrowthPositive depth (crossing depth) (selected depth).val
      (fun cfg => (actualFiniteAnnealedNaturalClock rule chemicalGrowth chemicalGrowthPositive depth natural.growth kind cfg : ℝ))
      (clockPositive depth kind) kind]
    exact (actualFiniteOriginalJointResponse_selected_identity rule marks chemicalGrowth chemicalGrowthPositive depth _ kind
      (initial depth marks)).symm

end
end IGSIII34.ResistanceLimit
