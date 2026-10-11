import IGSIII34.Spectral.Collars.RetainedSkeleton
import IGSIII34.Spectral.ActualNaturalSpectralWitnessCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology

local instance actualAtomlessMassCompletionMeasurable {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance actualAtomlessMassCompletionBorel {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- For the actual classical critical model the natural endpoint and its
Perron mass measure are constructed together. The mass has zero singletons
and gives zero mass to the actual persistent retained vertex skeleton.
Neither the endpoint nor the mass measure is supplied by the caller. -/
theorem exists_actual_natural_mass_null_singletons_and_skeleton
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint,
    ∃ weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address, Tendsto (fun depth =>
          markedOrientedVertexMass rule marks depth (componentEdgeAddress address)
            (retainedComponentState rule marks address) /
            markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
          atTop (𝓝 (weight address marks))) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) marks,
      ∃ compactness : CompactSpace (UniformSpace.Completion
        (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩))),
      letI := compactness
      ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
      ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
        ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩,
      weight [] marks = 1 ∧
      IsProbabilityMeasure boundary ∧
      (∀ depth word, boundary {path | path depth = word} =
        ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
      Measurable realization ∧
      (∀ᵐ path ∂boundary, ∀ depth,
        Fin.init (path (depth + 1)) = path depth ∧
          retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive) ∧
      (∀ᵐ path ∂boundary, Tendsto (fun depth =>
        actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          marks typical.1.1 depth (path (depth + 1))) atTop (𝓝 (realization path))) ∧
      IsProbabilityMeasure (boundary.map realization) ∧
      NullSingletonClass (boundary.map realization) ∧
      (boundary.map realization) (Set.range (UniformSpace.Completion.coe' (α :=
        ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩)))) = 0 := by
  obtain ⟨natural⟩ := exists_natural_resistance_completion20261011
    rule classicalRule p positive belowOne fixedPoint
  obtain ⟨continuation⟩ := exists_actual_mass_continuation_completion20261011
    rule classicalRule p positive belowOne fixedPoint
  obtain ⟨weight, actualRatios, witnesses⟩ := exists_ae_actual_natural_spectral_witness_completion20261011
    rule classicalRule p positive belowOne fixedPoint natural
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks := by
    filter_upwards [witnesses] with marks witness
    obtain ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, _⟩ := witness
    exact fun address => (positiveWeights address).1
  refine ⟨natural, weight, actualRatios, ?_⟩
  filter_upwards [witnesses, actual_physical_mass_null_singletons rule classicalRule p positive belowOne
    fixedPoint natural continuation weight actualRatios nonnegative] with marks witness zero
  obtain ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, measurable, retainedPaths, convergence, projections, massProbability,
    massOpenPositive, support, spectra⟩ := witness
  letI := compactness
  have nullSingletons := zero typical compactness boundary boundaryProbability atoms retainedPaths
    realization measurable convergence
  letI := nullSingletons
  refine ⟨typical, compactness, boundary, realization, rootWeight, boundaryProbability, atoms,
    measurable, retainedPaths, convergence, massProbability, nullSingletons, ?_⟩
  exact actual_stationary_retained_skeleton_zero_mass rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) ⟨marks, typical⟩) (boundary.map realization)

end
end IGSIII34.Spectral
