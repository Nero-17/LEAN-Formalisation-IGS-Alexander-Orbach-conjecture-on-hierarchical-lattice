import IGSIII34.Spectral.CollarSummabilityCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal Topology

/-- Boundary traces of the finite-generation planted skeleton. A trace
keeps touching a coarse planted terminal at every finer socket depth. -/
def terminalSkeletonBoundaryCompletion20261011 (rule : Rule) :
    Set (Π depth, Fin depth → (Fin rule.edges × Bool)) :=
  ⋃ coarseDepth : ℕ, ⋂ collarDepth : ℕ,
    terminalCylinderCollarCompletion20261011 rule 0 coarseDepth collarDepth

theorem actual_boundary_skeleton_zero_mass_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))),
      IsProbabilityMeasure boundary →
      (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) →
      boundary (terminalSkeletonBoundaryCompletion20261011 rule) = 0 := by
  have degreeStrict := classicalRule.terminal_degree_lt_mass_spectralRadius p positive belowOne
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _) degreeStrict
  have ratioNonnegative : 0 ≤ (rule.network.fullGraph.degree rule.network.source : ℝ) /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    div_nonneg (Nat.cast_nonneg _) radiusPositive.le
  have ratioBelowOne : (rule.network.fullGraph.degree rule.network.source : ℝ) /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal < 1 :=
    (div_lt_one radiusPositive).mpr degreeStrict
  have avoidance (coarseDepth : ℕ) := actual_boundary_collar_ae_avoidance_completion20261011
    rule classicalRule p positive belowOne fixedPoint continuation weight actualRatios nonnegative
    (fun _ => 0) (fun _ => coarseDepth) (fun index => index)
    (summable_geometric_of_lt_one ratioNonnegative ratioBelowOne)
  filter_upwards [ae_all_iff.mpr avoidance] with marks avoidances
  intro boundary probability atoms
  unfold terminalSkeletonBoundaryCompletion20261011
  apply measure_iUnion_null
  intro coarseDepth
  have noTrace : ∀ᵐ path ∂boundary,
      path ∉ ⋂ collarDepth : ℕ, terminalCylinderCollarCompletion20261011 rule 0 coarseDepth collarDepth := by
    filter_upwards [(avoidances coarseDepth boundary probability atoms).2] with path avoids
    obtain ⟨collarDepth, outside⟩ := avoids.exists
    exact fun member => outside (Set.mem_iInter.mp member collarDepth)
  simpa only [not_not, Set.setOf_mem_eq] using ae_iff.mp noTrace

/-- Every reciprocal-integer collar width is eventually avoided by a
typical actual boundary point, simultaneously. These widths tend to zero
and suffice for the arbitrary-exponent spectral localisation argument. -/
theorem actual_boundary_all_reciprocal_collars_avoided_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))),
      IsProbabilityMeasure boundary →
      (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) →
      ∀ᵐ path ∂boundary, ∀ divisor : ℕ, 0 < divisor → ∀ᶠ depth in atTop,
        path ∉ terminalCylinderCollarCompletion20261011 rule 0 depth (depth / divisor) := by
  have degreeStrict := classicalRule.terminal_degree_lt_mass_spectralRadius p positive belowOne
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _) degreeStrict
  have ratioNonnegative : 0 ≤ (rule.network.fullGraph.degree rule.network.source : ℝ) /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    div_nonneg (Nat.cast_nonneg _) radiusPositive.le
  have ratioBelowOne : (rule.network.fullGraph.degree rule.network.source : ℝ) /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal < 1 :=
    (div_lt_one radiusPositive).mpr degreeStrict
  have avoidance (divisor : ℕ) : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < divisor → ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))),
      IsProbabilityMeasure boundary →
      (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) →
      ∀ᵐ path ∂boundary, ∀ᶠ depth in atTop,
        path ∉ terminalCylinderCollarCompletion20261011 rule 0 depth (depth / divisor) := by
    by_cases positiveDivisor : 0 < divisor
    · have result := actual_boundary_collar_ae_avoidance_completion20261011
        rule classicalRule p positive belowOne fixedPoint continuation weight actualRatios nonnegative
        (fun _ => 0) (fun depth => depth) (fun depth => depth / divisor)
        (summable_geometric_nat_div_completion20261011 _ ratioNonnegative ratioBelowOne divisor positiveDivisor)
      exact result.mono (fun marks properties _ boundary probability atoms => (properties boundary probability atoms).2)
    · exact Eventually.of_forall (fun _ impossible => (positiveDivisor impossible).elim)
  filter_upwards [ae_all_iff.mpr avoidance] with marks avoidances
  intro boundary probability atoms
  apply ae_all_iff.mpr
  intro divisor
  by_cases positiveDivisor : 0 < divisor
  · exact (avoidances divisor positiveDivisor boundary probability atoms).mono (fun _ property _ => property)
  · exact Eventually.of_forall (fun _ impossible => (positiveDivisor impossible).elim)

end
end IGSIII34.Spectral
