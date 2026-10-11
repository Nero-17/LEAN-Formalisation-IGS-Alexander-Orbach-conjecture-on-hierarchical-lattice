import IGSIII34.Spectral.ActualNaturalSpectralWitnessCompletion20261011
import IGSIII34.Spectral.ActualTypicalSpectralDimensionCompletion20261011

/-! The natural resistance law, actual Perron mass measure and mass-typical
spectral limit are constructed from the classical critical innovation law.
No measure, spectral datum or exponent estimate is supplied by the caller.
Markov/path identification is proved in separate construction modules. -/
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

theorem exists_ae_actual_natural_typical_spectral_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
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
            Real.log (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth))) := by
  obtain ⟨continuation⟩ := exists_actual_mass_continuation_completion20261011 rule classicalRule p positive belowOne fixedPoint
  obtain ⟨weight, actualRatios, witnesses⟩ := exists_ae_actual_natural_spectral_witness_completion20261011
    rule classicalRule p positive belowOne fixedPoint natural
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks := by
    filter_upwards [witnesses] with marks witness
    obtain ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
      atoms, measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support, spectra⟩ := witness
    exact fun address => (positiveWeights address).1
  have exponents := ae_actual_typical_spectral_dimension_completion20261011 rule classicalRule p positive belowOne fixedPoint
    natural continuation weight actualRatios nonnegative
  refine ⟨weight, actualRatios, ?_⟩
  filter_upwards [witnesses, exponents] with marks witness exponent
  obtain ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support, spectra⟩ := witness
  letI := compactness
  letI := massProbability
  letI := massOpenPositive
  refine ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support, ?_⟩
  intro anchor
  obtain ⟨data⟩ := spectra anchor
  exact ⟨data, exponent typical compactness boundary boundaryProbability atoms retainedPaths
    realization measurable convergence massProbability massOpenPositive anchor data⟩

theorem exists_actual_classical_natural_typical_spectral_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    : ∃ natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint,
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
            Real.log (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth))) := by
  obtain ⟨natural⟩ := exists_natural_resistance_completion20261011 rule classicalRule p positive belowOne fixedPoint
  obtain ⟨weight, ratios, witness⟩ := exists_ae_actual_natural_typical_spectral_completion20261011
    rule classicalRule p positive belowOne fixedPoint natural
  exact ⟨natural, weight, ratios, witness⟩

end
end IGSIII34.Spectral
