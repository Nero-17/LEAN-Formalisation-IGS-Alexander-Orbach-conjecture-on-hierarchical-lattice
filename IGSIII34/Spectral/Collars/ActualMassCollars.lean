import IGSIII34.Spectral.Collars.LinearWidths
import IGSIII34.Spectral.Collars.MassLogarithm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology

/-- The Appendix B mass and linear collar conclusions on the actual
component boundary. The mass measure is constructed from the retained
vertex ratios on the original innovation tree. All conclusions hold on
one probability-one event, with no inverse mass moment hypothesis. -/
theorem exists_actual_typical_log_mass_and_linear_collars
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        weight [] marks = 1 ∧
        (∀ address, 0 ≤ weight address marks ∧
          weight address marks = ∑ choice : Fin rule.edges × Bool,
            weight (address ++ [choice]) marks ∧
          Tendsto (fun depth => markedOrientedVertexMass rule marks depth
            (componentEdgeAddress address) (retainedComponentState rule marks address) /
            markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
            atTop (𝓝 (weight address marks))) ∧
        ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
          IsProbabilityMeasure boundary ∧
          (∀ depth word, boundary {path | path depth = word} =
            ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
          boundary (terminalSkeletonBoundaryCompletion rule) = 0 ∧
          ∀ᵐ path ∂boundary,
            (∀ depth, Fin.init (path (depth + 1)) = path depth ∧
              0 < weight (List.ofFn (path depth)) marks) ∧
            Tendsto (fun depth : ℕ => Real.log (weight (List.ofFn (path depth)) marks) / depth)
              atTop (𝓝 (-Real.log
                ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))) ∧
            ∀ width : ℚ, 0 < width → ∀ᶠ depth in atTop,
              path ∉ terminalCylinderCollarCompletion rule 0 depth
                (Nat.ceil ((width : ℝ) * depth)) := by
  obtain ⟨weight, properties⟩ := exists_actual_typical_component_mass_completion
    classicalRule p positive belowOne fixedPoint
  obtain ⟨continuation⟩ := exists_actual_mass_continuation_completion
    rule classicalRule p positive belowOne fixedPoint
  have actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth => markedOrientedVertexMass rule marks depth
        (componentEdgeAddress address) (retainedComponentState rule marks address) /
        markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)) :=
    properties.mono (fun _ properties address => (properties.2.1 address).2.2)
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks :=
    properties.mono (fun _ properties address => (properties.2.1 address).1)
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _)
      (classicalRule.terminal_degree_lt_mass_spectralRadius p positive belowOne)
  refine ⟨weight, ?_⟩
  filter_upwards [properties,
    actual_boundary_skeleton_zero_mass_completion rule classicalRule p positive belowOne
      fixedPoint continuation weight actualRatios nonnegative,
    actual_boundary_all_rational_linear_collars_avoided rule classicalRule p positive belowOne
      fixedPoint continuation weight actualRatios nonnegative]
    with marks properties skeletonZero avoidances
  obtain ⟨boundary, probability, atoms, typicalMass⟩ := properties.2.2
  refine ⟨properties.1, properties.2.1, boundary, probability, atoms,
    skeletonZero boundary probability atoms, ?_⟩
  filter_upwards [typicalMass, avoidances boundary probability atoms] with path typical avoids
  refine ⟨typical.1, ?_, avoids⟩
  exact logarithmic_mass_limit_of_subexponential_bounds
    (fun depth => weight (List.ofFn (path depth)) marks) _ radiusPositive
    (fun depth => (typical.1 depth).2) typical.2

end
end IGSIII34.Spectral
