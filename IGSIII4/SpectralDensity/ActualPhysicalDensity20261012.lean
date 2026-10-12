import IGSIII4.SpectralDensity.ActualDensityCompletion20261012
import IGSIII4.SpectralDensity.ActualFamilyParameters20261012

/-! The actual spectral-density witnesses include the physical mass measure,
compact electrical space, spectral data and almost-everywhere heat-kernel
limit, all for the very same natural resistance completion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34 IGSIII34.Percolation
open IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII.Chemical.Substitution
open IGSIII34.Spectral MeasureTheory Filter Topology

local instance {Carrier : Type*} [UniformSpace Carrier] :
    MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance {Carrier : Type*} [UniformSpace Carrier] :
    BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- A physical typical-point spectral exponent for a specified natural
resistance completion. This records the constructed physical mass and
actual heat kernel, rather than only the numerical dimension formula. -/
def ActualPhysicalTypicalSpectralDimension20261012
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (dimension : ℝ) : Prop :=
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
          (𝓝[>] 0) (𝓝 dimension)

theorem actual_natural_physical_typical_dimension20261012
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ActualPhysicalTypicalSpectralDimension20261012 rule p positive belowOne fixedPoint natural
      (typicalSpectralDimension (actualMassGrowth rule p) natural.growth) := by
  simpa only [ActualPhysicalTypicalSpectralDimension20261012, typicalSpectralDimension, actualMassGrowth] using
    exists_ae_actual_natural_typical_spectral_completion20261011
      rule classicalRule p positive belowOne fixedPoint natural

/-- The numerical appendix exponent is realized by the physical heat kernel
for exactly the natural completion appearing in the density limit. -/
theorem appendix_actual_physical_typical_dimension20261012 (base : ℝ) (length : ℕ) :
    ActualPhysicalTypicalSpectralDimension20261012
      (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2))
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2
      (appendixNaturalCompletion base length)
      (typicalSpectralDimension
        (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
        (appendixNaturalCompletion base length).growth) :=
  actual_natural_physical_typical_dimension20261012
    (appendixRule base (max length 2)) (appendixRule_classical base _ (Nat.le_max_right _ _))
    (appendixCriticalProbability base (max length 2))
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2
    (appendixNaturalCompletion base length)

/-- The actual physical spectral exponents are dense in (1,2), already among
the explicit classical rules whose terminal distance, both terminal degrees
and minimum terminal edge cut are all two. Each rule uses its own interior
critical probability and exactly the natural completion used in the
resistance-growth estimates. -/
theorem actual_physical_spectral_density_two_terminal_parameters20261012
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2)
    (nonemptyInterval : lower < upper) :
    ∃ base : ℝ, 1 < base ∧ ∃ length : ℕ,
      (appendixRule base (max length 2)).Classical ∧
      (appendixRule base (max length 2)).network.fullGraph.dist
        (appendixRule base (max length 2)).network.source
        (appendixRule base (max length 2)).network.target = 2 ∧
      (appendixRule base (max length 2)).network.fullGraph.degree
        (appendixRule base (max length 2)).network.source = 2 ∧
      (appendixRule base (max length 2)).network.fullGraph.degree
        (appendixRule base (max length 2)).network.target = 2 ∧
      (appendixRule base (max length 2)).network.terminalEdgeConnectivity = 2 ∧
      0 < appendixCriticalProbability base (max length 2) ∧
      appendixCriticalProbability base (max length 2) < 1 ∧
      (appendixRule base (max length 2)).network.reliability
        (appendixCriticalProbability base (max length 2)) =
          appendixCriticalProbability base (max length 2) ∧
      typicalSpectralDimension
        (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
        (appendixNaturalCompletion base length).growth ∈ Set.Ioo lower upper ∧
      ActualPhysicalTypicalSpectralDimension20261012
        (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2))
        (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
        (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1
        (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2
        (appendixNaturalCompletion base length)
        (typicalSpectralDimension
          (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
          (appendixNaturalCompletion base length).growth) := by
  obtain ⟨base, baseAboveOne, length, dimensionInInterval⟩ :=
    appendix_actual_spectral_density20261012 lower upper lowerAboveOne upperBelowTwo nonemptyInterval
  obtain ⟨distance, sourceDegree, targetDegree, connectivity⟩ :=
    appendixRule_terminal_parameters20261012 base (max length 2) (Nat.le_max_right _ _)
  exact ⟨base, baseAboveOne, length, appendixRule_classical base _ (Nat.le_max_right _ _),
    distance, sourceDegree, targetDegree, connectivity,
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1,
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1,
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2,
    dimensionInInterval, appendix_actual_physical_typical_dimension20261012 base length⟩

end
end IGSIII4.SpectralDensity.ActualFamily
