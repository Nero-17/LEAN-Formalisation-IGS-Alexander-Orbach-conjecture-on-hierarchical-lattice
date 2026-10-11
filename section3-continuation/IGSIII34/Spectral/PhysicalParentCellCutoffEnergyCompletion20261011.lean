import IGSIII34.Spectral.PhysicalElectricalInverseMaximaCompletion20261011
import IGSIII34.Spectral.ActualCellCutoffSupportCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators Topology

/-- The actual harmonic cutoff energy equals its finite trace energy and
is bounded by the number of genuinely varying trace edges. All electrical
inverse factors have been bounded on the original innovation law. -/
theorem physical_harmonic_cutoff_energy_subexponential_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ threshold : ℕ, ∀ depth : ℕ, threshold ≤ depth + 1 →
        ∀ (typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks)
          (boundary : Fin (rule.generation depth).vertices → ℝ),
        (∀ vertex, 0 ≤ boundary vertex ∧ boundary vertex ≤ 1) →
        ∀ support : Finset {edge : Fin (rule.generation depth).edges // stationaryConfiguration rule marks depth edge = true},
        (∀ edge, (network (rule.generation depth).network (stationaryConfiguration rule marks depth)).graph.Reachable
          (rule.generation depth).network.source ((rule.generation depth).network.endpoint edge.val).1 →
          edge ∉ support → boundary ((rule.generation depth).network.endpoint edge.val).1 =
            boundary ((rule.generation depth).network.endpoint edge.val).2) →
        limitingEnergy
          (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))
          (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))
          (actualHarmonicFunction rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ depth boundary) ≤
        (support.card : ℝ) * natural.growth^(depth + 1) * slack^(depth + 1) := by
  filter_upwards [physical_electrical_inverse_alladdress_subexponential_completion20261011
    rule p positive belowOne fixedPoint natural] with marks maxima
  intro slack greater
  obtain ⟨threshold, estimates⟩ := maxima slack greater
  refine ⟨threshold, ?_⟩
  intro depth after typical boundary range support variationSupported
  rw [actualHarmonicFunction_limiting_energy]
  have traceBound := source_trace_cutoff_energy_bound_completion20261011
    (network (rule.generation depth).network (stationaryConfiguration rule marks depth))
    (stationaryResistance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks depth)
    boundary range support variationSupported
    (natural.growth^(depth + 1) * slack^(depth + 1))
    (mul_nonneg (pow_nonneg (zero_lt_one.trans natural.aboveOne).le _) (pow_nonneg (zero_lt_one.trans greater).le _))
    (fun edge member => by
      have estimate := estimates (generationEdgeAddress rule depth edge.val) (by
        simpa only [generationEdgeAddress_length] using after)
      simp only [stationaryResistance, stationaryGenerationResistance, List.nil_append,
        mul_inv_rev, inv_pow, inv_inv]
      simpa only [generationEdgeAddress_length, mul_comm] using
        mul_le_mul_of_nonneg_left estimate (pow_nonneg (zero_lt_one.trans natural.aboveOne).le (depth + 1)))
  simpa only [mul_assoc] using traceBound

/-- On the original innovation law, a binary harmonic cutoff supported in
a genuine parent cell costs only the number of its refined physical edges.
The multiplicative electrical error is subexponential at all addresses. -/
theorem physical_parent_cell_harmonic_cutoff_energy_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ threshold : ℕ, ∀ coarse fine : ℕ,
        threshold ≤ coarse + fine + 2 →
        ∀ (typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks)
          (parent : Fin (rule.generation coarse).edges)
          (selected : Finset (Fin (rule.generation (coarse + fine + 1)).vertices)),
        (∀ vertex ∈ selected, ∃ inside : (rule.generation fine).network.InteriorVertex,
          (generationBlockCellEmbedding rule coarse fine parent).vertex inside.val = vertex) →
        limitingEnergy
          (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))
          (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))
          (actualHarmonicFunction rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ (coarse + fine + 1)
            (fun vertex => if vertex ∈ selected then 1 else 0)) ≤
        (rule.edges : ℝ)^(fine + 1) * natural.growth^(coarse + fine + 2) * slack^(coarse + fine + 2) := by
  classical
  filter_upwards [physical_harmonic_cutoff_energy_subexponential_completion20261011
      rule p positive belowOne fixedPoint natural] with marks estimates
  intro slack greater
  obtain ⟨threshold, estimates⟩ := estimates slack greater
  refine ⟨threshold, ?_⟩
  intro coarse fine after typical parent selected internal
  have estimate := estimates (coarse + fine + 1) (by omega) typical
    (fun vertex => if vertex ∈ selected then 1 else 0)
    (fun vertex => by by_cases member : vertex ∈ selected <;> simp [member])
    (openedCellEdgeSupportCompletion20261011 (generationBlockCellEmbedding rule coarse fine parent)
      (stationaryConfiguration rule marks (coarse + fine + 1)))
    (fun edge _ outside => actual_binary_cell_boundary_supported_completion20261011
      rule coarse fine parent (stationaryConfiguration rule marks (coarse + fine + 1)) selected internal edge outside)
  have supportCount := actual_opened_cell_edge_support_count_completion20261011 rule coarse fine parent
    (stationaryConfiguration rule marks (coarse + fine + 1))
  have realCount :
      ((openedCellEdgeSupportCompletion20261011 (generationBlockCellEmbedding rule coarse fine parent)
        (stationaryConfiguration rule marks (coarse + fine + 1))).card : ℝ) ≤ (rule.edges : ℝ)^(fine + 1) := by
    exact_mod_cast supportCount
  have firstNonnegative := pow_nonneg (zero_lt_one.trans natural.aboveOne).le (coarse + fine + 2)
  have lastNonnegative := pow_nonneg (zero_lt_one.trans greater).le (coarse + fine + 2)
  exact estimate.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right realCount firstNonnegative) lastNonnegative)

end
end IGSIII34.Spectral

