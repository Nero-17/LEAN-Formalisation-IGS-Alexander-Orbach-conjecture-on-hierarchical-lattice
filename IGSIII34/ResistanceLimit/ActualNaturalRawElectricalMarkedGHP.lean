import IGSIII34.ResistanceLimit.RawElectricalMarkedGHP
import IGSIII34.Diffusion.ActualNaturalCountingMassCompletion
import IGSIII34.Diffusion.ActualNaturalDegreeMassCompletion

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

local instance naturalRawElectricalGHPMeasurable {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance naturalRawElectricalGHPBorel {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- Both original finite mass conventions converge in the raw electrical
metric using the same actual boundary realization and natural scalar. -/
theorem ae_actual_natural_raw_electrical_markedGHP
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
      ∀ typical : StationaryElectricalTypical rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) marks,
      ∀ compactness : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩),
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundary)
        (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word) marks)),
      ∀ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
          ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩,
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          marks typical depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0) →
      ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
      MarkedGHPConverges
        (fun depth => RawElectricalFiniteCluster rule (stationaryConfiguration rule marks) natural.growth (zero_lt_one.trans natural.aboveOne) depth)
        (actualFiniteClusterMeasure rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive)
        (boundary.map realization)
        (rawElectricalTerminal rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩)
        (actualElectricalTerminal rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) ∧
      MarkedGHPConverges
        (fun depth => RawElectricalFiniteCluster rule (stationaryConfiguration rule marks) natural.growth (zero_lt_one.trans natural.aboveOne) depth)
        (actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks)
          (fun depth => markedGenerationConfiguration_crosses rule marks typical.2.1 depth [] true)
          chemicalScale chemicalScalePositive)
        (boundary.map realization)
        (rawElectricalTerminal rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩)
        (actualElectricalTerminal rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, endpointFixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  have growthPositive := zero_lt_one.trans natural.aboveOne
  obtain ⟨eta, inverseBelowEta, etaBelowOne⟩ := exists_between (inv_lt_one_of_one_lt₀ natural.aboveOne)
  have etaPositive := (inv_pos.mpr growthPositive).trans inverseBelowEta
  have productGreaterThanOne : 1 < natural.growth * eta := by
    have multiplied := mul_lt_mul_of_pos_left inverseBelowEta growthPositive
    simpa only [mul_inv_cancel₀ growthPositive.ne'] using multiplied
  filter_upwards [
    ae_actual_natural_counting_mass_tendsto_completion rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative,
    ae_actual_natural_degree_mass_tendsto_completion rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive growthPositive growthBounds (natural.amplitude • natural.field) endpointFixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
      endpointFixed membership eta etaPositive etaBelowOne productGreaterThanOne]
    with marks counting degrees fields mesh
  obtain ⟨start, radiusBounds⟩ := mesh
  intro typical compactness boundary probability atoms realization projection chemicalScale chemicalScalePositive
  letI := compactness
  constructor
  · apply actual_raw_electrical_markedGHP rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive ⟨marks, typical⟩ fields
      eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne radiusBounds
    exact counting typical boundary probability atoms realization projection chemicalScale chemicalScalePositive
  · apply actual_raw_electrical_markedGHP rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive ⟨marks, typical⟩ fields
      eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne radiusBounds
    exact degrees typical boundary probability atoms realization projection chemicalScale chemicalScalePositive

end
end IGSIII34.ResistanceLimit
