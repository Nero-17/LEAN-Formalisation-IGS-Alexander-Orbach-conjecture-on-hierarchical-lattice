import IGSIII34.Diffusion.ActualNaturalVertexSpeedCadlagCompletion
import IGSIII34.Diffusion.ActualCommonVertexSpeedChemicalCadlagCompletion
import IGSIII34.Diffusion.ActualVertexSpeedCadlagLawCompletion
import IGSIII34.Diffusion.ActualContinuousCadlagWholeWeakCompletion
import IGSIII34.Diffusion.ActualContinuousLimitAssemblyCompletion
import IGSIII34.Diffusion.ActualNaturalDegreeMassCompletion
import IGSIII34.Diffusion.ActualResolventUniformCompletion
import IGSIII34.Spectral.ActualNaturalSpectralWitnessCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII34.Spectral
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance rawNaturalVertexChemicalCompletionMeasurableCompletion {Carrier : Type*} [UniformSpace Carrier] : MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance rawNaturalVertexChemicalCompletionBorelCompletion {Carrier : Type*} [UniformSpace Carrier] : BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- The original natural field supplies all electrical convergence and mesh
inputs. Any actual Perron boundary realization with the same vertex ratios
therefore has whole finite-resolvent convergence on the genuine paper clock. -/
local instance rawNaturalVertexChemicalContinuousMeasurableCompletion {Space : Type*} [TopologicalSpace Space] : MeasurableSpace C(ℝ≥0, Space) := borel _
local instance rawNaturalVertexChemicalContinuousBorelCompletion {Space : Type*} [TopologicalSpace Space] : BorelSpace C(ℝ≥0, Space) := ⟨rfl⟩
local instance rawNaturalVertexChemicalCarrierMeasurableCompletion (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance rawNaturalVertexChemicalCarrierBorelCompletion (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩
theorem ae_actual_natural_vertex_speed_chemical_common_completion
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

        Tendsto (fun depth => actualVertexVariableSpeedCadlagLawCompletion rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩
          chemicalScale chemicalScalePositive depth (initial depth)) atTop
          (𝓝 (continuousCadlagProbabilityCompletion limitLaw (countableTimeContinuousSampleCompletion times dense) (countableTimeContinuousSample_continuous_completion times dense) (countableTimeContinuousSample_evaluation_measurable_completion times dense))) ∧
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
      ∀ chemicalCompactness : CompactSpace (actualStationaryChemicalSpaceCompletion rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) harmonicMarks classicalRule chemicalScale chemicalScalePositive
        lengths lengthNonnegative lengthPositive childConvergence),
      letI := chemicalCompactness
    ∃ Ambient : Type, ∃ ambientMetric : MetricSpace Ambient,
      letI := ambientMetric
      ∃ complete : CompleteSpace Ambient,
      ∃ compact : CompactSpace Ambient,
      letI := complete
      letI := compact
      ∃ target : actualStationaryChemicalSpaceCompletion rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) harmonicMarks classicalRule
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → Ambient,
      ∃ targetIsometry : Isometry target,
      ∃ sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule harmonicMarks.val)
        chemicalScale chemicalScalePositive depth → Ambient,
      (∀ depth, Isometry (sources depth)) ∧
      letI : MeasurableSpace Ambient := borel Ambient
      letI : BorelSpace Ambient := ⟨rfl⟩
      let homeomorph := actualChemicalElectricalCarrierHomeomorphCompletion rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
        harmonicMarks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
        chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
      Tendsto (fun depth => actualVertexVariableSpeedPlacedCadlagLawCompletion rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) harmonicMarks chemicalScale chemicalScalePositive depth (initial depth) (sources depth)) atTop
        (𝓝 ((continuousCadlagProbabilityCompletion limitLaw (countableTimeContinuousSampleCompletion times dense) (countableTimeContinuousSample_continuous_completion times dense) (countableTimeContinuousSample_evaluation_measurable_completion times dense)).map (skorokhodCadlagContinuousCarrierMap_continuous_completion
          (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable)) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, endpointFixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  have growthPositive := zero_lt_one.trans natural.aboveOne
  have physicalPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < (natural.amplitude • natural.field) marks := by
    filter_upwards [Lp.coeFn_smul natural.amplitude natural.field, natural.fieldPositive] with marks scalar fieldPositive
    rw [scalar]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (zero_lt_one.trans_le natural.amplitudeLower) fieldPositive
  obtain ⟨eta, inverseBelowEta, etaBelowOne⟩ := exists_between (inv_lt_one_of_one_lt₀ natural.aboveOne)
  have etaPositive := (inv_pos.mpr growthPositive).trans inverseBelowEta
  have productGreaterThanOne : 1 < natural.growth * eta := by
    have multiplied := mul_lt_mul_of_pos_left inverseBelowEta growthPositive
    simpa only [mul_inv_cancel₀ growthPositive.ne'] using multiplied
  filter_upwards [ae_actual_natural_vertex_speed_cadlag_completion rule classicalRule p positive belowOne fixedPoint
      natural weight actualRatios nonnegative,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint natural.growth growthPositive (natural.amplitude • natural.field) physicalPositive endpointFixed,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant natural.growth constantPositive growthPositive
      growthBounds (natural.amplitude • natural.field) endpointFixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant natural.growth constantPositive natural.aboveOne
      growthBounds (natural.amplitude • natural.field) endpointFixed membership eta etaPositive etaBelowOne productGreaterThanOne]
    with marks convergence stationary fields mesh
  obtain ⟨start, radiusBounds⟩ := mesh
  refine ⟨eta, ((rule.edges + 1 : ℝ) / (1 - eta)), start, etaPositive.le, etaBelowOne, radiusBounds, stationary, fields, ?_⟩
  intro typical compactness
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
    (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
  intro boundary probability atoms realization projection massProbability massOpenPositive
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  intro chemicalScale chemicalScalePositive anchor data initial times timeZero dense initialLimit initialConvergence
  obtain ⟨limitLaw, weak⟩ := convergence typical compactness boundary probability atoms realization projection massProbability massOpenPositive
    chemicalScale chemicalScalePositive anchor data initial times timeZero dense initialLimit initialConvergence
  refine ⟨limitLaw, weak, ?_⟩
  let harmonicMarks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks} := ⟨marks, typical⟩
  dsimp only
  intro lengths lengthNonnegative lengthPositive childConvergence chemicalEta chemicalCoefficient chemicalStart
    chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds chemicalCompactness
  letI := chemicalCompactness
  exact actual_vertex_speed_common_chemical_cadlag_transfer_completion
    rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
    harmonicMarks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary fields eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne radiusBounds
    chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
    initial (continuousCadlagProbabilityCompletion limitLaw (countableTimeContinuousSampleCompletion times dense)
      (countableTimeContinuousSample_continuous_completion times dense)
      (countableTimeContinuousSample_evaluation_measurable_completion times dense)) weak

end
end IGSIII34.Diffusion