import IGSIII34.Spectral.Collars.ActualSameMasterAllClocks
import IGSIII34.ResistanceLimit.ActualSameCarrierMeasuredMarkedState
import IGSIII34.Diffusion.IntrinsicJointGHPPathTest
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

local instance sectionThreeAnnealedJointTests_ActualNaturalConstructedDiffusionWitnessLocal1 {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance sectionThreeAnnealedJointTests_ActualNaturalConstructedDiffusionWitnessLocal2 {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance sectionThreeAnnealedJointTests_ActualNaturalConstructedDiffusionWitnessCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance sectionThreeAnnealedJointTests_ActualNaturalConstructedDiffusionWitnessCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance sectionThreeAnnealedJointTests_ActualNaturalConstructedDiffusionWitnessCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance sectionThreeAnnealedJointTests_actualNaturalConstructedDiffusionWitnessCompleteCompletion20261011 : CompleteSpace
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

local instance sectionThreeAnnealedJointTests_exactChemicalCarrierMeasurable : MeasurableSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := borel _
local instance sectionThreeAnnealedJointTests_exactChemicalCarrierBorel : BorelSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩

theorem exists_ae_actual_natural_common_section_three_annealed_joint_tests
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∃ chemicalGrowth : ℝ, ∃ chemicalGrowthPositive : 0 < chemicalGrowth,
    ∃ amplitude : ℝ, ∃ amplitudeAtLeastOne : 1 ≤ amplitude, ∃ chemicalValue : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
      ∃ (edgeCoefficient vertexCoefficient : ℝ)
        (mass : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      0 < edgeCoefficient ∧ 0 < vertexCoefficient ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < mass marks ∧
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
      IsProbabilityMeasure boundary ∧
      Measurable realization ∧
      ∃ massProbability : IsProbabilityMeasure (boundary.map realization),
      ∃ massOpenPositive : (boundary.map realization).IsOpenPosMeasure,
      letI := massProbability
      letI := massOpenPositive
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
      ∃ sourcesIsometry : ∀ depth, Isometry (sources depth),
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
      (Tendsto (fun depth =>
        ProbabilityMeasure.map (⟨actualFiniteClusterMeasure rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth, inferInstance⟩ : ProbabilityMeasure
          (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth))
            (measurable_of_finite (sources depth)).aemeasurable) atTop
        (𝓝 (ProbabilityMeasure.map (⟨boundary.map realization, massProbability⟩ : ProbabilityMeasure
          (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩))
          (targetIsometry.continuous.comp homeomorph.symm.continuous).measurable.aemeasurable)) ∧
      Tendsto (fun depth => levyProkhorovEDist ((actualFiniteClusterMeasure rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth).map (sources depth))
        ((boundary.map realization).map (target ∘ homeomorph.symm))) atTop (𝓝 0)) ∧
      (Tendsto (fun depth =>
        ProbabilityMeasure.map (⟨actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks) (fun depth => markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true) chemicalGrowth chemicalGrowthPositive depth, inferInstance⟩ : ProbabilityMeasure
          (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalGrowth chemicalGrowthPositive depth))
            (measurable_of_finite (sources depth)).aemeasurable) atTop
        (𝓝 (ProbabilityMeasure.map (⟨boundary.map realization, massProbability⟩ : ProbabilityMeasure
          (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks,typical.1.1⟩))
          (targetIsometry.continuous.comp homeomorph.symm.continuous).measurable.aemeasurable)) ∧
      Tendsto (fun depth => levyProkhorovEDist ((actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks) (fun depth => markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true) chemicalGrowth chemicalGrowthPositive depth).map (sources depth))
        ((boundary.map realization).map (target ∘ homeomorph.symm))) atTop (𝓝 0)) ∧
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
      (∀ test : IntrinsicJointGHPPathTest,
        (∀ countingSpeed : Bool, Tendsto (fun depth => ∫ path, test.value Ambient (states depth) path ∂(actualPaperDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalGrowth chemicalGrowthPositive countingSpeed depth (initial depth) (sources depth) : Measure _)) atTop
        (𝓝 (∫ path, test.value Ambient state path ∂(((continuousCadlagProbabilityCompletion20261011 limitLaw
          (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))
          (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
          (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense ((Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks)))) * time))).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable) : Measure _)))) ∧
        Tendsto (fun depth => ∫ path, test.value Ambient (states depth) path ∂(actualPaperDiscreteDeterministicPlacedCadlagLaw rule classicalRule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalGrowth chemicalGrowthPositive depth (initial depth) (sources depth) : Measure _)) atTop
        (𝓝 (∫ path, test.value Ambient state path ∂(((continuousCadlagProbabilityCompletion20261011 limitLaw
          (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path ((Real.toNNReal (1 / (2 * (edgeCoefficient * mass marks)))) * time))
          (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
          (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense ((Real.toNNReal (1 / (2 * (edgeCoefficient * mass marks)))) * time))).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable) : Measure _))) ∧
        Tendsto (fun depth => ∫ path, test.value Ambient (states depth) path ∂(actualPaperPlacedDiscreteCadlagLaw rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive initial sources depth : Measure _)) atTop
        (𝓝 (∫ path, test.value Ambient state path ∂(((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable) : Measure _))) ∧
        Tendsto (fun depth => ∫ path, test.value Ambient (states depth) path ∂(actualPaperPlacedContinuousCadlagLaw rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive initial sources depth : Measure _)) atTop
        (𝓝 (∫ path, test.value Ambient state path ∂(((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable) : Measure _))) ∧
        Tendsto (fun depth => ∫ path, test.value Ambient (states depth) path ∂(actualVertexVariableSpeedPlacedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks,typical⟩
        chemicalGrowth chemicalGrowthPositive depth (initial depth) (sources depth) : Measure _)) atTop
        (𝓝 (∫ path, test.value Ambient state path ∂(((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
          (countableTimeContinuousSample_continuous_completion20261011 times dense)
          (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
          (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
            (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable) : Measure _)))) ∧
      Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011
        rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩
        chemicalGrowth chemicalGrowthPositive times initial depth) atTop (𝓝 limitLaw)) := by
  have frozenMaster := exists_ae_actual_natural_common_section_three_all_clocks
    rule classicalRule p positive belowOne fixedPoint natural
  rcases frozenMaster with ⟨chemicalGrowth, chemicalGrowthPositive, amplitude, amplitudeAtLeastOne, chemicalValue,
    weight, ratios, edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, models⟩
  refine ⟨chemicalGrowth, chemicalGrowthPositive, amplitude, amplitudeAtLeastOne, chemicalValue,
    edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, ?_⟩
  refine models.mono ?_
  intro marks model
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
  refine ⟨massPositive, typical, compactness, boundary, realization, probability, measurable,
    massProbability, massOpenPositive, lengthNonnegative, lengthPositive, childConvergence,
    homeomorph, Ambient, ambientMetric, complete, compact, target, targetIsometry, sources,
    sourcesIsometry, placementClose, diracCompatibility, countingPlaced, degreePlaced, ?_⟩
  intro finiteStates limitState anchor
  have processWitness := processes anchor
  rcases processWitness with ⟨data, process⟩
  refine ⟨data, ?_⟩
  intro initial times timeZero dense initialLimit initialConvergence
  have limitWitness := process initial times timeZero dense initialLimit initialConvergence
  rcases limitWitness with ⟨limitLaw, observedWeak, deterministic, remaining⟩
  rcases remaining with ⟨initialLaw, regular, continuous, continuousWeak, cadlagWeak,
    placedDiscreteWeak, placedContinuousWeak, placedVertexWeak, rest⟩
  refine ⟨limitLaw, ?_, observedWeak⟩
  intro test
  refine ⟨fun countingSpeed => ?_, ?_, ?_, ?_, ?_⟩
  · exact intrinsic_joint_test_response_tendsto test states state _ _ spatial (deterministic countingSpeed).1.1
  · exact intrinsic_joint_test_response_tendsto test states state _ _ spatial (deterministic false).2.1
  · exact intrinsic_joint_test_response_tendsto test states state _ _ spatial placedDiscreteWeak
  · exact intrinsic_joint_test_response_tendsto test states state _ _ spatial placedContinuousWeak
  · exact intrinsic_joint_test_response_tendsto test states state _ _ spatial placedVertexWeak


end
end IGSIII34.ResistanceLimit
