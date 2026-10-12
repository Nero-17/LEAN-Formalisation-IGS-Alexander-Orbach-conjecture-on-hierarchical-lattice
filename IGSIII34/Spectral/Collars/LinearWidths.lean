import IGSIII34.Spectral.BoundarySkeletonCompletion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology BigOperators

/-- The precise ceiling schedule in Appendix B is summable. The proof
compares it with a reciprocal integer schedule, including ratio zero. -/
theorem summable_geometric_linear_ceiling
    (ratio width : ℝ) (nonnegative : 0 ≤ ratio) (belowOne : ratio < 1)
    (positiveWidth : 0 < width) :
    Summable (fun depth : ℕ => ratio ^ Nat.ceil (width * depth)) := by
  obtain ⟨divisor, reciprocalBelow⟩ := exists_nat_one_div_lt positiveWidth
  apply Summable.of_nonneg_of_le (fun _ => pow_nonneg nonnegative _) _
    (summable_geometric_nat_div_completion ratio nonnegative belowOne
      (divisor + 1) (Nat.succ_pos _))
  intro depth
  apply pow_le_pow_of_le_one nonnegative belowOne.le
  apply (Nat.cast_le (α := ℝ)).mp
  calc
    ((depth / (divisor + 1) : ℕ) : ℝ) ≤ (depth : ℝ) / (divisor + 1 : ℕ) := Nat.cast_div_le
    _ ≤ width * depth := by
      have comparison := mul_le_mul_of_nonneg_right reciprocalBelow.le (Nat.cast_nonneg depth)
      simpa only [Nat.cast_add, Nat.cast_one, one_div, div_eq_mul_inv, one_mul, mul_comm] using comparison
    _ ≤ (Nat.ceil (width * depth) : ℝ) := Nat.le_ceil _

/-- On one event for the original innovation law, every positive rational
linear collar width is eventually avoided at almost every boundary point.
The physical collars and their mass estimates are those of the actual
substitution, and no collar estimate is an input. -/
theorem actual_boundary_all_rational_linear_collars_avoided
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address)
          (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
      IsProbabilityMeasure boundary →
      (∀ depth word, boundary {path | path depth = word} =
        ENNReal.ofReal (weight (List.ofFn word) marks)) →
      ∀ᵐ path ∂boundary, ∀ width : ℚ, 0 < width → ∀ᶠ depth in atTop,
        path ∉ terminalCylinderCollarCompletion rule 0 depth
          (Nat.ceil ((width : ℝ) * depth)) := by
  have degreeStrict := classicalRule.terminal_degree_lt_mass_spectralRadius p positive belowOne
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _) degreeStrict
  have ratioNonnegative : 0 ≤ (rule.network.fullGraph.degree rule.network.source : ℝ) /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    div_nonneg (Nat.cast_nonneg _) radiusPositive.le
  have ratioBelowOne : (rule.network.fullGraph.degree rule.network.source : ℝ) /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal < 1 :=
    (div_lt_one radiusPositive).mpr degreeStrict
  have avoidance (width : ℚ) : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < width → ∀ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
      IsProbabilityMeasure boundary →
      (∀ depth word, boundary {path | path depth = word} =
        ENNReal.ofReal (weight (List.ofFn word) marks)) →
      ∀ᵐ path ∂boundary, ∀ᶠ depth in atTop,
        path ∉ terminalCylinderCollarCompletion rule 0 depth
          (Nat.ceil ((width : ℝ) * depth)) := by
    by_cases positiveWidth : 0 < width
    · have result := actual_boundary_collar_ae_avoidance_completion
        rule classicalRule p positive belowOne fixedPoint continuation weight actualRatios nonnegative
        (fun _ => 0) (fun depth => depth) (fun depth => Nat.ceil ((width : ℝ) * depth))
        (summable_geometric_linear_ceiling _ _ ratioNonnegative ratioBelowOne
          (by exact_mod_cast positiveWidth))
      exact result.mono (fun marks properties _ boundary probability atoms =>
        (properties boundary probability atoms).2)
    · exact Eventually.of_forall (fun _ impossible => (positiveWidth impossible).elim)
  filter_upwards [ae_all_iff.mpr avoidance] with marks avoidances
  intro boundary probability atoms
  apply ae_all_iff.mpr
  intro width
  by_cases positiveWidth : 0 < width
  · exact (avoidances width positiveWidth boundary probability atoms).mono
      (fun _ property _ => property)
  · exact Eventually.of_forall (fun _ impossible => (positiveWidth impossible).elim)

end
end IGSIII34.Spectral
