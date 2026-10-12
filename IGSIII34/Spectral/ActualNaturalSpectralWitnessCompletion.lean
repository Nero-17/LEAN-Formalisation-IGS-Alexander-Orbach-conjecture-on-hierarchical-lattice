import IGSIII34.Spectral.ActualSpectralDataCompletion
import IGSIII34.Forms.ActualFormMassWitnessCompletion
import IGSIII34.ResistanceLimit.ActualElectricalMassRetainedCompletion
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion

/-! The actual physical natural endpoint, Perron mass and spectral data
are assembled on one event of the original critical innovation law.
No compact carrier, mass measure or dense energy-domain hypothesis is
left to the caller. Markov/path conclusions are separate targets. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped _root_.Topology

local instance {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

theorem exists_ae_actual_natural_spectral_witness_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ∃ weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
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
      ∀ anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩),
      Nonempty (ActualSpectralDataCompletion rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
        anchor (boundary.map realization)) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, endpointFixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  have growthPositive := zero_lt_one.trans natural.aboveOne
  have inverseBelowOne : natural.growth⁻¹ < 1 := inv_lt_one_of_one_lt₀ natural.aboveOne
  obtain ⟨eta, lowerEta, etaBelowOne⟩ := exists_between inverseBelowOne
  have etaPositive := (inv_pos.mpr growthPositive).trans lowerEta
  have productGreaterThanOne : 1 < natural.growth * eta := by
    have multiplied := mul_lt_mul_of_pos_left lowerEta growthPositive
    simpa only [mul_inv_cancel₀ growthPositive.ne'] using multiplied
  obtain ⟨weight, actualRatios, masses⟩ := exists_ae_actual_electrical_mass_retained_fixed_cluster_completion rule classicalRule p positive belowOne fixedPoint
    constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
    endpointFixed membership eta etaPositive etaBelowOne productGreaterThanOne
  refine ⟨weight, actualRatios, ?_⟩
  filter_upwards [masses,
    ae_actualCompletionEnergyDomain_dense_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
      endpointFixed membership eta etaPositive etaBelowOne productGreaterThanOne] with marks witness regular
  obtain ⟨electricalTypical, electricalCompactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, retainedPaths, measurable, massProbability, massOpenPositive, support, convergence, projections⟩ := witness
  obtain ⟨typical, compactness, density⟩ := regular
  letI := compactness
  letI := massProbability
  letI := massOpenPositive
  refine ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support, ?_⟩
  intro anchor
  exact exists_actual_spectral_data_completion rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
    anchor (boundary.map realization) density

end
end IGSIII34.Spectral
