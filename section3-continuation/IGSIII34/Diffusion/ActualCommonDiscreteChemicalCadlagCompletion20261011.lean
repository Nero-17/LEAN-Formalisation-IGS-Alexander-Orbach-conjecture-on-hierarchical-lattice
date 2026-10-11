import IGSIII34.Diffusion.ActualChemicalCadlagLawCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteCadlagWholeWeakCompletion20261011
import IGSIII34.Diffusion.DiscreteCadlagWeakCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalCommonRealisationCompletion20261011

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

local instance actualCommonDiscreteChemicalCadlagCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualCommonDiscreteChemicalCadlagCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualCommonDiscreteChemicalCadlagCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualCommonDiscreteChemicalCadlagCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualCommonDiscreteChemicalCadlagCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualCommonDiscreteChemicalCadlagNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualCommonDiscreteChemicalCadlagCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualCommonDiscreteChemicalCadlagNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualCommonDiscreteChemicalCadlagTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualCommonDiscreteChemicalCadlagNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualCommonDiscreteChemicalCadlagInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualCommonDiscreteChemicalCadlagCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

variable (classicalRule : rule.Classical) (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

variable (chemicalEta chemicalCoefficient : ℝ) (chemicalStart : ℕ)
  (chemicalEtaNonnegative : 0 ≤ chemicalEta) (chemicalEtaBelowOne : chemicalEta < 1)
  (chemicalCoefficientNonnegative : 0 ≤ chemicalCoefficient)
  (chemicalRadiusBounds : ∀ address opened depth, chemicalStart ≤ address.length →
    (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
      chemicalCoefficient * chemicalEta ^ address.length)
variable [CompactSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)]
local instance commonDiscreteChemicalCadlagCarrierMeasurableCompletion20261011 : MeasurableSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := borel _
local instance commonDiscreteChemicalCadlagCarrierBorelCompletion20261011 : BorelSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩

local instance commonDiscreteChemicalCadlagElectricalCompletionCompactCompletion20261011 : CompactSpace
    (ElectricalSpace rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
  infer_instance


include anchor chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds in
/-- The original discrete simple random walks converge on genuine whole
cadlag paths in the same common isometric chemical realization. The
limiting process is the constructed electrical diffusion transported
through the proved chemical carrier homeomorphism. -/
theorem actual_discrete_common_chemical_cadlag_whole_weak_completion20261011
    (edgePositive : 0 < rule.edges) (growthGreaterThanOne : 1 < growth)
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
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
    (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times)
    (initialLimit : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (initialConvergence : Tendsto (fun depth => (initial depth).map
      (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)).aemeasurable)
      atTop (𝓝 initialLimit)) :
    ∃ (Ambient : Type) (ambientMetric : MetricSpace Ambient),
      letI := ambientMetric
      letI : MeasurableSpace Ambient := borel Ambient
      letI : BorelSpace Ambient := ⟨rfl⟩
      ∃ complete : CompleteSpace Ambient,
      ∃ compact : CompactSpace Ambient,
      letI := complete
      letI := compact
      ∃ target : actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → Ambient,
      ∃ targetIsometry : Isometry target,
      ∃ sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
        chemicalScale chemicalScalePositive depth → Ambient,
        (∀ depth, Isometry (sources depth)) ∧
        ∃ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩),
          Tendsto (fun depth => actualPaperDiscreteElectricalCadlagLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
            marks chemicalScale chemicalScalePositive initial depth) atTop (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
              (countableTimeContinuousSample_continuous_completion20261011 times dense)
              (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense))) ∧
          let homeomorph := actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
                marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
                stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne radiusBound
                chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
          Tendsto (fun depth => discreteCadlagProbabilityCompletion20261011
            (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
            (Space := Ambient)
            (⟨finiteDiscreteWalkLaw (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
              (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
              (initial depth : Measure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)), inferInstance⟩ :
                ProbabilityMeasure (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
            (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩ depth)
            (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth)
            (sources depth)) atTop
            (𝓝 ((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense)
              (countableTimeContinuousSample_continuous_completion20261011 times dense)
              (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map
              (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 (target ∘ homeomorph.symm)
                (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable)) := by
  obtain ⟨limitLaw, canonicalWeak⟩ := actual_discrete_cadlag_whole_weak_convergence_completion20261011
    rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor
    edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBound data initial times timeZero dense initialLimit initialConvergence
  obtain ⟨Ambient, ambientMetric, complete, compact, target, targetIsometry, sources, sourcesIsometric, placementClose⟩ :=
    exists_actual_chemical_common_isometric_realisation_completion20261011 rule classicalRule marks.val marks.property.1.1.2.1
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
  letI := ambientMetric
  letI : CompleteSpace Ambient := complete
  letI : CompactSpace Ambient := compact
  letI : MeasurableSpace Ambient := borel Ambient
  letI : BorelSpace Ambient := ⟨rfl⟩
  letI : MeasurableSpace (ElectricalSpace rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2) := borel _
  letI : BorelSpace (ElectricalSpace rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2) := ⟨rfl⟩
  let homeomorph := actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
                marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
                stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne radiusBound
                chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
  refine ⟨Ambient, ambientMetric, complete, compact, target, targetIsometry, sources, sourcesIsometric, limitLaw, canonicalWeak, ?_⟩
  apply discreteCadlagProbability_common_embedding_weak_completion20261011
    (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (fun depth => (⟨finiteDiscreteWalkLaw
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
      (initial depth : Measure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)), inferInstance⟩ :
        ProbabilityMeasure (ℕ → ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)))
    (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)
    (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth)
    sources _ canonicalWeak
  intro tolerance tolerancePositive
  filter_upwards [placementClose tolerance tolerancePositive] with depth close
  intro vertex
  have birthIdentity := actualChemicalElectricalCarrierHomeomorph_symm_birth_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne radiusBound
    chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds depth vertex
  change homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex) = _ at birthIdentity
  change dist (sources depth vertex)
    (target (homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex))) < tolerance
  rw [birthIdentity]
  exact close vertex

end
end IGSIII34.Diffusion

