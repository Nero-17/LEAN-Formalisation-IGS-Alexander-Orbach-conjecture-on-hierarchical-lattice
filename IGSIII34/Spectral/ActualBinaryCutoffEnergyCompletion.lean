import IGSIII34.Spectral.ElectricalInverseMaximaCompletion
import IGSIII34.ResistanceLimit.ActualHarmonic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators Topology

theorem source_trace_cutoff_energy_bound_completion
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (potential : Vertex → ℝ) (range : ∀ vertex, 0 ≤ potential vertex ∧ potential vertex ≤ 1)
    (support : Finset Edge)
    (variationSupported : ∀ edge, network.graph.Reachable network.source (network.endpoint edge).1 →
      edge ∉ support → potential (network.endpoint edge).1 = potential (network.endpoint edge).2)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (conductanceBound : ∀ edge ∈ support, (resistance edge)⁻¹ ≤ bound) :
    sourceComponentEnergy network resistance potential ≤ (support.card : ℝ) * bound := by
  classical
  unfold sourceComponentEnergy finiteEnergy
  calc
    _ ≤ ∑ edge : Edge, if edge ∈ support then bound else 0 := by
      apply Finset.sum_le_sum
      intro edge _
      dsimp only at ⊢
      by_cases member : edge ∈ support
      · rw [if_pos member]
        by_cases retained : network.graph.Reachable network.source (network.endpoint edge).1
        · rw [if_pos retained]
          have squareBound : (potential (network.endpoint edge).1 - potential (network.endpoint edge).2)^2 ≤ 1 := by
            obtain ⟨firstNonnegative, firstBelow⟩ := range (network.endpoint edge).1
            obtain ⟨lastNonnegative, lastBelow⟩ := range (network.endpoint edge).2
            nlinarith [mul_nonneg firstNonnegative lastNonnegative,
              mul_nonneg (sub_nonneg.mpr firstBelow) (sub_nonneg.mpr lastBelow)]
          simpa only [mul_one] using mul_le_mul (conductanceBound edge member) squareBound (sq_nonneg _) boundNonnegative
        · simp only [if_neg retained, zero_mul]
          exact boundNonnegative
      · rw [if_neg member]
        by_cases retained : network.graph.Reachable network.source (network.endpoint edge).1
        · rw [if_pos retained, variationSupported edge retained member, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
        · simp only [if_neg retained, zero_mul]
          exact le_rfl
    _ = _ := by rw [← Finset.sum_filter]; simp

/-- The actual harmonic cutoff energy equals its finite trace energy and
is bounded by the number of genuinely varying trace edges. All electrical
inverse factors have been bounded on the original innovation law. -/
theorem actual_harmonic_cutoff_energy_subexponential_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ threshold : ℕ, ∀ depth : ℕ, threshold ≤ depth + 1 →
        ∀ (typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth natural.field marks)
          (boundary : Fin (rule.generation depth).vertices → ℝ),
        (∀ vertex, 0 ≤ boundary vertex ∧ boundary vertex ≤ 1) →
        ∀ support : Finset {edge : Fin (rule.generation depth).edges // stationaryConfiguration rule marks depth edge = true},
        (∀ edge, (network (rule.generation depth).network (stationaryConfiguration rule marks depth)).graph.Reachable
          (rule.generation depth).network.source ((rule.generation depth).network.endpoint edge.val).1 →
          edge ∉ support → boundary ((rule.generation depth).network.endpoint edge.val).1 =
            boundary ((rule.generation depth).network.endpoint edge.val).2) →
        limitingEnergy
          (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth natural.field
            (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth natural.field ⟨marks, typical⟩))
          (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth natural.field
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth natural.field ⟨marks, typical⟩))
          (actualHarmonicFunction rule p positive belowOne fixedPoint natural.growth natural.field
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ depth boundary) ≤
        (support.card : ℝ) * natural.growth^(depth + 1) * slack^(depth + 1) := by
  filter_upwards [actual_electrical_inverse_alladdress_subexponential_completion
    rule p positive belowOne fixedPoint natural] with marks maxima
  intro slack greater
  obtain ⟨threshold, estimates⟩ := maxima slack greater
  refine ⟨threshold, ?_⟩
  intro depth after typical boundary range support variationSupported
  rw [actualHarmonicFunction_limiting_energy]
  have traceBound := source_trace_cutoff_energy_bound_completion
    (network (rule.generation depth).network (stationaryConfiguration rule marks depth))
    (stationaryResistance rule p positive belowOne fixedPoint natural.growth natural.field marks depth)
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

end
end IGSIII34.Spectral
