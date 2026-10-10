import IGSIII.Mass.ComponentCylinderWeights
import IGSIII.Mass.CylinderBoundaryLaw

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

/-- The actual vertex-mass limits define a probability law on nested retained
components. In particular a B child is sampled through its two original sides,
and almost every sampled prefix belongs to a single live component. -/
theorem actual_component_boundary_probability_law {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
        weight [] marks = 1 ∧
        (∀ address, 0 ≤ weight address marks ∧
          weight address marks = ∑ choice : Fin rule.edges × Bool, weight (address ++ [choice]) marks ∧
          Tendsto (fun n => markedOrientedVertexMass rule marks n (componentEdgeAddress address) (retainedComponentState rule marks address) /
            markedOrientedVertexMass rule marks (n + address.length) [] .connected) atTop (𝓝 (weight address marks)) ∧
          (retainedComponentState rule marks address = .inactive → weight address marks = 0) ∧
          (retainedComponentState rule marks address = .connected → 0 < weight address marks)) ∧
        ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
          IsProbabilityMeasure boundary ∧
          (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
          ∀ᵐ path ∂boundary, ∀ depth,
            Fin.init (path (depth + 1)) = path depth ∧
            0 < weight (List.ofFn (path depth)) marks ∧
            retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive ∧
            retainedComponentState rule marks (List.ofFn (path depth)) ≠ .both := by
  classical
  obtain ⟨weight, properties⟩ := actual_component_cylinder_probability_weights classicalRule p positive below_one fixed_point
  refine ⟨weight, ?_⟩
  filter_upwards [properties] with marks properties
  have nonnegative : ∀ address, 0 ≤ weight address marks := fun address => (properties.2.1 address).1
  have compatible : ∀ address, weight address marks =
      ∑ choice : Fin rule.edges × Bool, weight (address ++ [choice]) marks := fun address => (properties.2.1 address).2.1
  obtain ⟨_, fallback_edge, _⟩ := rule.network.exists_pivotal_configuration (classicalRule.connected _)
  let fallback : Fin rule.edges × Bool := (fallback_edge, true)
  let boundary := cylinderBoundaryLaw fallback (fun address => weight address marks)
    nonnegative properties.1 compatible
  have probability : IsProbabilityMeasure boundary := cylinderBoundaryLaw_probability fallback
    (fun address => weight address marks) nonnegative properties.1 compatible
  refine ⟨properties.1, properties.2.1, boundary, probability, ?_, ?_⟩
  · intro depth word
    exact cylinderBoundaryLaw_atom fallback (fun address => weight address marks) nonnegative
      properties.1 compatible depth word
  change ∀ᵐ path ∂cylinderBoundaryLaw fallback (fun address => weight address marks) nonnegative properties.1 compatible, _
  filter_upwards [cylinderBoundaryLaw_extends fallback
      (fun address => weight address marks) nonnegative properties.1 compatible,
    cylinderBoundaryLaw_positive_prefixes fallback
      (fun address => weight address marks) nonnegative properties.1 compatible] with path nested positive_prefixes
  intro depth
  refine ⟨nested depth, positive_prefixes depth, ?_, retainedComponentState_ne_both rule marks _⟩
  intro inactive
  have zero_weight := (properties.2.1 (List.ofFn (path depth))).2.2.2.1 inactive
  exact (positive_prefixes depth).ne' zero_weight

end
end IGSIII.Chemical.Substitution
