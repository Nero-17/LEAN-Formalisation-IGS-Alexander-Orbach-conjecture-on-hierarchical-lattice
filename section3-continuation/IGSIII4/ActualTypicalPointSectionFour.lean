import IGSIII4.ActualSectionFour
import IGSIII34.Spectral.ActualNaturalTypicalSpectralCompletion20261011

/-! Section 4 for the actual constructed compact diffusion heat kernel.
Natural resistance, physical mass, compact carrier and spectral data are all
constructed. No accepted spectral formula or mass-ratio convergence is an
input to the final classical-rule theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34 IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open IGSIII34.Spectral MeasureTheory Filter Matrix
open scoped BigOperators _root_.Topology

local instance {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

theorem exists_ae_actual_section_four_typical_heat_kernel
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (chemical : ActualChemicalSectionTwo rule p positive belowOne fixedPoint) :
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
      ∃ dimension : ℝ,
        Tendsto (fun time => -2 * Real.log (actualSpectralHeatKernelCompletion20261011
          rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization) data time point point) / Real.log time)
          (𝓝[>] 0) (𝓝 dimension) ∧
        dimension = typicalSpectralDimension (actualMassGrowth rule p) natural.growth ∧
        (dimension = (4 / 3 : ℝ) ↔ actualMassGrowth rule p = natural.growth ^ 2) ∧
        (dimension = (4 / 3 : ℝ) ↔
          chemicalMassDimension (actualMassGrowth rule p) chemical.growth =
            2 * chemicalResistanceDimension natural.growth chemical.growth) ∧
        (¬ ((4 / 3 : ℝ) < chemicalMassDimension (actualMassGrowth rule p) chemical.growth ∧
          chemicalMassDimension (actualMassGrowth rule p) chemical.growth < 2 ∧
          (2 / 3 : ℝ) < chemicalResistanceDimension natural.growth chemical.growth ∧
          chemicalResistanceDimension natural.growth chemical.growth < 1) → dimension ≠ (4 / 3 : ℝ)) ∧
        (2 ≤ chemicalMassDimension (actualMassGrowth rule p) chemical.growth → (4 / 3 : ℝ) < dimension) ∧
        (chemicalMassDimension (actualMassGrowth rule p) chemical.growth ≤ (4 / 3 : ℝ) → dimension < (4 / 3 : ℝ)) := by
  obtain ⟨weight, actualRatios, witnesses⟩ :=
    exists_ae_actual_natural_typical_spectral_completion20261011
      rule classicalRule p positive belowOne fixedPoint natural
  have conclusions := section_four_for_natural_resistance
    rule classicalRule p positive belowOne fixedPoint natural chemical
  refine ⟨weight, actualRatios, ?_⟩
  filter_upwards [witnesses] with marks witness
  obtain ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support, spectra⟩ := witness
  letI := compactness
  letI := massProbability
  letI := massOpenPositive
  refine ⟨typical, compactness, boundary, realization, rootWeight, positiveWeights, boundaryProbability,
    atoms, measurable, retainedPaths, convergence, projections, massProbability, massOpenPositive, support, ?_⟩
  intro anchor
  obtain ⟨data, exponents⟩ := spectra anchor
  refine ⟨data, ?_⟩
  filter_upwards [exponents] with point limit
  exact ⟨typicalSpectralDimension (actualMassGrowth rule p) natural.growth, limit, rfl,
    conclusions.aoMassEquality, conclusions.aoDimensionEquality, conclusions.aoRegion,
    conclusions.largeMassSign, conclusions.smallMassSign⟩

theorem exists_actual_section_four_and_typical_heat_kernel
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    : ∃ natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint,
      ∃ chemical : ActualChemicalSectionTwo rule p positive belowOne fixedPoint,
      SectionFourConclusions rule p positive belowOne fixedPoint
        (naturalSectionFourElectrical rule p positive belowOne fixedPoint natural) chemical ∧
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
      ∃ dimension : ℝ,
        Tendsto (fun time => -2 * Real.log (actualSpectralHeatKernelCompletion20261011
          rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization) data time point point) / Real.log time)
          (𝓝[>] 0) (𝓝 dimension) ∧
        dimension = typicalSpectralDimension (actualMassGrowth rule p) natural.growth ∧
        (dimension = (4 / 3 : ℝ) ↔ actualMassGrowth rule p = natural.growth ^ 2) ∧
        (dimension = (4 / 3 : ℝ) ↔
          chemicalMassDimension (actualMassGrowth rule p) chemical.growth =
            2 * chemicalResistanceDimension natural.growth chemical.growth) ∧
        (¬ ((4 / 3 : ℝ) < chemicalMassDimension (actualMassGrowth rule p) chemical.growth ∧
          chemicalMassDimension (actualMassGrowth rule p) chemical.growth < 2 ∧
          (2 / 3 : ℝ) < chemicalResistanceDimension natural.growth chemical.growth ∧
          chemicalResistanceDimension natural.growth chemical.growth < 1) → dimension ≠ (4 / 3 : ℝ)) ∧
        (2 ≤ chemicalMassDimension (actualMassGrowth rule p) chemical.growth → (4 / 3 : ℝ) < dimension) ∧
        (chemicalMassDimension (actualMassGrowth rule p) chemical.growth ≤ (4 / 3 : ℝ) → dimension < (4 / 3 : ℝ)) := by
  obtain ⟨natural⟩ := exists_natural_resistance_completion20261011
    rule classicalRule p positive belowOne fixedPoint
  obtain ⟨chemical⟩ := exists_actual_chemical_section_two
    rule classicalRule p positive belowOne fixedPoint
  exact ⟨natural, chemical,
    section_four_for_natural_resistance rule classicalRule p positive belowOne fixedPoint natural chemical,
    exists_ae_actual_section_four_typical_heat_kernel
      rule classicalRule p positive belowOne fixedPoint natural chemical⟩

/-- The original global AO question, now stated for actual constructed
natural resistance. This definition is a conjecture predicate, not a proof. -/
def NaturalGlobalAlexanderOrbachConjecture : Prop :=
  ∀ (rule : Rule), rule.Classical → ∀ (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (natural : NaturalResistanceCompletion20261011 rule probability positive belowOne fixedPoint),
      actualMassGrowth rule probability ≠ natural.growth ^ 2

end
end IGSIII4
