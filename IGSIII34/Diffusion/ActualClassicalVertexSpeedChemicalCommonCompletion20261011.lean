import IGSIII34.Diffusion.ActualNaturalVertexSpeedChemicalCommonCompletion20261011
import IGSIII34.Diffusion.ActualClassicalVertexSpeedCadlagWitnessCompletion20261011
import IGSIII34.Diffusion.ActualNaturalVertexSpeedCadlagWitnessCompletion20261011
import IGSIII34.Diffusion.ActualNaturalVertexSpeedCadlagCompletion20261011
import IGSIII34.Spectral.ActualNaturalTypicalSpectralCompletion20261011
import IGSIII34.Spectral.ActualSpectralDataCompletion20261011
import IGSIII34.Forms.ActualFormMassWitnessCompletion20261011
import IGSIII34.ResistanceLimit.ActualElectricalMassRetainedCompletion20261011
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion20261011

/-! The actual physical natural endpoint, Perron mass and spectral data
are assembled on one event of the original critical innovation law.
The natural law, Perron mass and spectral data are constructed internally.
The original vertex-speed path laws also converge in the true common
chemical realization supplied by the actual Section 2 geometry. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.Spectral
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance ActualClassicalVertexSpeedChemicalCommonCompletion20261011Local1 {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance ActualClassicalVertexSpeedChemicalCommonCompletion20261011Local2 {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

theorem exists_actual_classical_vertex_speed_chemical_common_spectral_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint,
    ∃ weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address, Tendsto (fun depth =>
          markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
            markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
          atTop (𝓝 (weight address marks))) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
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
      (∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
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

        Tendsto (fun depth => actualVertexVariableSpeedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩
          chemicalScale chemicalScalePositive depth (initial depth)) atTop
          (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense) (countableTimeContinuousSample_continuous_completion20261011 times dense) (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)))) ∧

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
            Real.log (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)))) ∧
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ electricalEta electricalCoefficient : ℝ,
      ∃ electricalStart : ℕ,
      ∃ electricalEtaNonnegative : 0 ≤ electricalEta,
      ∃ electricalEtaBelowOne : electricalEta < 1,
      ∃ electricalRadiusBounds : ∀ address opened depth, electricalStart ≤ address.length →
        markedElectricalRadius rule marks depth address opened / natural.growth ^ (depth + 1 + address.length) ≤
          electricalCoefficient * electricalEta ^ address.length,
      ∃ stationary : ∀ address, electricalCell rule.network (marks (address, true))
        (fun edge => electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) (address ++ [edge]) marks) =
          natural.growth * electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) address marks,
      ∃ fieldLimit : ∀ address, Tendsto (fun depth => natural.growth⁻¹ ^ depth * electricalIteration rule marks depth address)
        atTop (𝓝 (electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) address marks)),
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

        Tendsto (fun depth => actualVertexVariableSpeedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩
          chemicalScale chemicalScalePositive depth (initial depth)) atTop
          (𝓝 (continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense) (countableTimeContinuousSample_continuous_completion20261011 times dense) (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense))) ∧
      let harmonicMarks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks} := ⟨marks, typical⟩
      letI : CompactSpace (ElectricalSpace rule (stationaryConfiguration rule harmonicMarks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨harmonicMarks.val,harmonicMarks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) harmonicMarks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨harmonicMarks.val,harmonicMarks.property.1.1⟩)
        harmonicMarks.property.1.1.2.2) := compactness
      ∀ lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ,
      ∀ lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge,
      ∀ lengthPositive : ∀ depth edge, stationaryConfiguration rule marks depth edge = true → 0 < lengths depth edge,
      ∀ childConvergence : ∀ coarse edge, Tendsto (fun fine =>
        (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
          (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
          chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)),
      ∀ chemicalEta chemicalCoefficient : ℝ,
      ∀ chemicalStart : ℕ,
      ∀ chemicalEtaNonnegative : 0 ≤ chemicalEta,
      ∀ chemicalEtaBelowOne : chemicalEta < 1,
      ∀ chemicalCoefficientNonnegative : 0 ≤ chemicalCoefficient,
      ∀ chemicalRadiusBounds : ∀ address opened depth, chemicalStart ≤ address.length →
        (markedTerminalComponentRadius rule marks depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
          chemicalCoefficient * chemicalEta ^ address.length,
      ∀ chemicalCompactness : CompactSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) harmonicMarks classicalRule chemicalScale chemicalScalePositive
        lengths lengthNonnegative lengthPositive childConvergence),
      letI := chemicalCompactness
    ∃ Ambient : Type, ∃ ambientMetric : MetricSpace Ambient,
      letI := ambientMetric
      ∃ complete : CompleteSpace Ambient,
      ∃ compact : CompactSpace Ambient,
      letI := complete
      letI := compact
      ∃ target : actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) harmonicMarks classicalRule
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → Ambient,
      ∃ targetIsometry : Isometry target,
      ∃ sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule harmonicMarks.val)
        chemicalScale chemicalScalePositive depth → Ambient,
      (∀ depth, Isometry (sources depth)) ∧
      letI : MeasurableSpace Ambient := borel Ambient
      letI : BorelSpace Ambient := ⟨rfl⟩
      let homeomorph := actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
        harmonicMarks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
        chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
      Tendsto (fun depth => actualVertexVariableSpeedPlacedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) harmonicMarks chemicalScale chemicalScalePositive depth (initial depth) (sources depth)) atTop
        (𝓝 ((continuousCadlagProbabilityCompletion20261011 limitLaw (countableTimeContinuousSampleCompletion20261011 times dense) (countableTimeContinuousSample_continuous_completion20261011 times dense) (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)).map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
          (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable)) := by
  obtain ⟨natural, weight, ratios, witness⟩ := exists_actual_classical_vertex_speed_cadlag_spectral_witness_completion20261011
    rule classicalRule p positive belowOne fixedPoint
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks := by
    filter_upwards [witness] with marks model
    obtain ⟨typical, compactness, boundary, realization, _, positiveWeights, _⟩ := model
    exact fun address => (positiveWeights address).1
  refine ⟨natural, weight, ⟨ratios, witness⟩, ?_⟩
  exact ae_actual_natural_vertex_speed_chemical_common_completion20261011 rule classicalRule p positive belowOne fixedPoint
    natural weight ratios nonnegative

end
end IGSIII34.Diffusion