import IGSIII34.Diffusion.ActualNaturalClockCorrectorCompletion20261011
import IGSIII34.Diffusion.ActualAdditiveClockCompletion20261011
import IGSIII34.Diffusion.ActualNaturalDegreeMassCompletion20261011
import IGSIII34.Diffusion.ActualNaturalCountingMassCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

local instance ActualNaturalAdditiveClockCompletion20261011CompletionMeasurable {Carrier : Type*} [UniformSpace Carrier] : MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance ActualNaturalAdditiveClockCompletion20261011CompletionBorel {Carrier : Type*} [UniformSpace Carrier] : BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩
local instance ActualNaturalAdditiveClockCompletion20261011PhysicalMeasurable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance ActualNaturalAdditiveClockCompletion20261011PhysicalBorel (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

theorem ae_actual_natural_additive_clock_prefix_probability_tendsto_completion20261011
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
      ∀ compactness : CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))),
      letI := compactness
      letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundary)
        (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word) marks)),
      ∀ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩,
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1))))
        (boundary.map realization)) atTop (𝓝 0) →
      ∀ massProbability : IsProbabilityMeasure (boundary.map realization),
      ∀ massOpenPositive : (boundary.map realization).IsOpenPosMeasure,
      letI := massProbability
      letI := massOpenPositive
      ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
      ∀ initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth),
      ∀ (horizon radius : ℝ), 0 ≤ horizon → 0 < radius →
      Tendsto (fun depth =>
        (finiteDiscreteWalkLaw (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth)
          (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth))
          (cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks depth)
            (markedGenerationConfiguration_crosses rule marks typical.1.1.2.1 depth [] true)) (initial depth : Measure _)).real
          {path | ∃ prefixLength ≤ ⌊(2 * Fintype.card (ClusterEdge (rule.generation depth).network
              (stationaryConfiguration rule marks depth)) * natural.growth ^ (depth+1)) * horizon⌋₊,
            radius ≤ |finiteWalkScaledAdditiveCompletion20261011
              (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth)) * natural.growth ^ (depth+1))
              (actualCountingClockCenteredForcingCompletion20261011 rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth)
              prefixLength path|}) atTop (𝓝 0) := by
  filter_upwards [ae_actual_natural_clock_corrector_uniform_zero_completion20261011 rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative,
    ae_actualCountingClock_density_bound_completion20261011 rule classicalRule p positive belowOne fixedPoint]
    with marks correctors density
  intro typical compactness
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
    (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
  intro boundary probability atoms realization projection massProbability massOpenPositive
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  intro chemicalScale chemicalScalePositive initial horizon radius horizonNonnegative radiusPositive
  obtain ⟨bound, boundPositive, bounded⟩ := density chemicalScale chemicalScalePositive
  apply actual_additive_clock_prefix_probability_tendsto_completion20261011 rule marks typical.1.1.2.1
    chemicalScale chemicalScalePositive natural.growth (zero_lt_one.trans natural.aboveOne) initial
    (bound+1) (by linarith) (fun depth vertex => (bounded depth vertex).2) ?_
    horizon radius horizonNonnegative radiusPositive
  exact correctors typical compactness boundary probability atoms realization projection massProbability massOpenPositive
    chemicalScale chemicalScalePositive 1 zero_lt_one

end
end IGSIII34.Diffusion