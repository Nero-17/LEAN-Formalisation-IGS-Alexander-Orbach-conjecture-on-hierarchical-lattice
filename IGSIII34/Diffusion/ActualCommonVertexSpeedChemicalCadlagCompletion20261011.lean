import IGSIII34.ResistanceLimit.ActualCarrierHomeomorphBirthCompletion20261011
import IGSIII34.Diffusion.FiniteWeightedCommonEmbeddingCompletion20261011
import IGSIII34.Diffusion.ActualVertexSpeedCadlagLawCompletion20261011
import IGSIII34.Diffusion.ActualVertexSpeedChemicalCadlagLawCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalCommonRealisationCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.ResistanceLimit
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Spectral IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

variable (classicalRule : rule.Classical) (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

variable
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (electricalEta electricalCoefficient : ℝ) (electricalStart : ℕ)
    (electricalEtaNonnegative : 0 ≤ electricalEta) (electricalEtaBelowOne : electricalEta < 1)
    (electricalRadiusBounds : ∀ address opened depth, electricalStart ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        electricalCoefficient * electricalEta ^ address.length)
    (chemicalEta chemicalCoefficient : ℝ) (chemicalStart : ℕ)
    (chemicalEtaNonnegative : 0 ≤ chemicalEta) (chemicalEtaBelowOne : chemicalEta < 1)
    (chemicalCoefficientNonnegative : 0 ≤ chemicalCoefficient)
    (chemicalRadiusBounds : ∀ address opened depth, chemicalStart ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        chemicalCoefficient * chemicalEta ^ address.length)

variable [CompactSpace (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)]
local instance commonVertexChemicalCadlagCarrierMeasurableCompletion20261011 : MeasurableSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := borel _
local instance commonVertexChemicalCadlagCarrierBorelCompletion20261011 : BorelSpace
    (actualStationaryChemicalSpaceCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩

local instance commonVertexElectricalChemicalCadlagCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := borel _
local instance commonVertexElectricalChemicalCadlagCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)]

local instance commonVertexChemicalCadlagElectricalCompletionCompactCompletion20261011 : CompactSpace
    (ElectricalSpace rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
  infer_instance

/-- The exact variable-speed law with an arbitrary placement. -/
def actualVertexVariableSpeedPlacedCadlagLawCompletion20261011
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (placement : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  let endpoint := clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let degreePositive := cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  exact finiteWeightedCadlagProbabilityCompletion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    endpoint degreePositive initial
    (finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) endpoint)
    (finiteCountingClockDensity_positive_completion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) endpoint degreePositive)
    (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth + 1))
    (by positivity) placement

include stationary fieldLimit electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds in
/-- Transport helper for the already proved canonical variable-speed law.
The common ambient and all source isometries are constructed from actual
chemical distance convergence. The canonical weak input is eliminated by
the separate raw natural-model caller. -/
theorem actual_vertex_speed_common_chemical_cadlag_transfer_completion20261011
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)))
    (projectedWeak : Tendsto (fun depth => actualVertexVariableSpeedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩ chemicalScale chemicalScalePositive depth (initial depth)) atTop (𝓝 law)) :
    ∃ Ambient : Type, ∃ ambientMetric : MetricSpace Ambient,
      letI := ambientMetric
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
      letI : MeasurableSpace Ambient := borel Ambient
      letI : BorelSpace Ambient := ⟨rfl⟩
      let homeomorph := actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
        chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
      Tendsto (fun depth => actualVertexVariableSpeedPlacedCadlagLawCompletion20261011 rule p positive belowOne fixedPoint
        growth value growthPositive marks chemicalScale chemicalScalePositive depth (initial depth) (sources depth)) atTop
        (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
          (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)).measurable.aemeasurable)) := by
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
  letI : ∀ depth, Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    fun depth => ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  let endpoint := fun depth => clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let degreePositive := fun depth => cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  letI : ∀ depth, Nonempty (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :=
    fun depth => clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  let homeomorph := actualChemicalElectricalCarrierHomeomorphCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
    chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds
  refine ⟨Ambient, ambientMetric, complete, compact, target, targetIsometry, sources, sourcesIsometric, ?_⟩
  apply finiteWeightedCadlagProbability_common_embedding_weak_completion20261011
    (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (fun depth => ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    endpoint degreePositive initial
    (fun depth => finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) (endpoint depth))
    (fun depth => finiteCountingClockDensity_positive_completion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) (endpoint depth) (degreePositive depth))
    (fun depth => 2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) * growth ^ (depth + 1))
    (fun depth => by positivity)
    (target ∘ homeomorph.symm) (targetIsometry.continuous.comp homeomorph.symm.continuous)
    (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth)
    sources law projectedWeak
  intro tolerance tolerancePositive
  filter_upwards [placementClose tolerance tolerancePositive] with depth close
  intro vertex
  have birthIdentity := actualChemicalElectricalCarrierHomeomorph_symm_birth_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary fieldLimit electricalEta electricalCoefficient electricalStart electricalEtaNonnegative electricalEtaBelowOne electricalRadiusBounds
    chemicalEta chemicalCoefficient chemicalStart chemicalEtaNonnegative chemicalEtaBelowOne chemicalCoefficientNonnegative chemicalRadiusBounds depth vertex
  change homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex) = _ at birthIdentity
  change dist (sources depth vertex)
    (target (homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex))) < tolerance
  rw [birthIdentity]
  exact close vertex

end
end IGSIII34.Diffusion

