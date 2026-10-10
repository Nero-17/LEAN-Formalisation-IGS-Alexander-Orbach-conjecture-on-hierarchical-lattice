import IGSIII.Mass.RetainedCylinderWeights

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter
open scoped BigOperators Topology

/-- A B socket supplies its original two components separately. Other live
states have one component, so the unused branch is inactive. -/
def componentChildState : OrientedState → Bool → OrientedState
  | .connected, true => .connected
  | .both, true => .sourceOnly
  | .both, false => .targetOnly
  | .sourceOnly, true => .sourceOnly
  | .targetOnly, false => .targetOnly
  | _, _ => .inactive

theorem componentChildState_ne_both (parent : OrientedState) (side : Bool) :
    componentChildState parent side ≠ .both := by
  cases parent <;> cases side <;> decide

theorem componentChildState_mass_sum (mass : OrientedState → ℝ)
    (inactive_zero : mass .inactive = 0) (both_split : mass .both = mass .sourceOnly + mass .targetOnly)
    (parent : OrientedState) : ∑ side : Bool, mass (componentChildState parent side) = mass parent := by
  cases parent <;> simp only [Fintype.sum_bool, componentChildState, inactive_zero, both_split, add_zero, add_comm]

def componentEdgeAddress {edges : ℕ} (address : List (Fin edges × Bool)) : List (Fin edges) := address.map Prod.fst

def retainedComponentStateFrom (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    List (Fin rule.edges) → OrientedState → List (Fin rule.edges × Bool) → OrientedState
  | _, parent, [] => parent
  | ancestor, parent, choice :: tail => retainedComponentStateFrom rule marks (ancestor ++ [choice.1])
      (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (ancestor, parent.massOpened)) choice.1) choice.2) tail

def retainedComponentState (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges × Bool)) : OrientedState :=
  retainedComponentStateFrom rule marks [] .connected address

theorem retainedComponentStateFrom_ne_both (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (ancestor : List (Fin rule.edges)) (parent : OrientedState) (parent_ne_both : parent ≠ .both)
    (address : List (Fin rule.edges × Bool)) :
    retainedComponentStateFrom rule marks ancestor parent address ≠ .both := by
  induction address generalizing ancestor parent with
  | nil => exact parent_ne_both
  | cons choice tail induction_hypothesis =>
      exact induction_hypothesis _ _ (componentChildState_ne_both _ _)

theorem retainedComponentState_ne_both (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges × Bool)) : retainedComponentState rule marks address ≠ .both :=
  retainedComponentStateFrom_ne_both rule marks [] .connected (by decide) address

theorem retainedComponentStateFrom_append (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (ancestor : List (Fin rule.edges)) (parent : OrientedState) (first second : List (Fin rule.edges × Bool)) :
    retainedComponentStateFrom rule marks ancestor parent (first ++ second) =
      retainedComponentStateFrom rule marks (ancestor ++ componentEdgeAddress first)
        (retainedComponentStateFrom rule marks ancestor parent first) second := by
  induction first generalizing ancestor parent with
  | nil => simp only [List.nil_append, componentEdgeAddress, List.map_nil, List.append_nil, retainedComponentStateFrom]
  | cons choice tail induction_hypothesis =>
    simp only [List.cons_append, retainedComponentStateFrom]
    rw [induction_hypothesis]
    simp only [componentEdgeAddress, List.map_cons, List.append_assoc, List.singleton_append]

theorem retainedComponentState_append_singleton (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges × Bool)) (choice : Fin rule.edges × Bool) :
    retainedComponentState rule marks (address ++ [choice]) =
      componentChildState (rule.network.orientedChildState (retainedComponentState rule marks address).sourceSelected
        (retainedComponentState rule marks address).targetSelected
        (marks (componentEdgeAddress address, (retainedComponentState rule marks address).massOpened)) choice.1) choice.2 := by
  rw [retainedComponentState, retainedComponentStateFrom_append]
  simp only [List.nil_append, retainedComponentStateFrom, retainedComponentState]

def componentCylinderWeight (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (cylinder : List (Fin rule.edges) → OrientedState → ℝ) (address : List (Fin rule.edges × Bool)) : ℝ :=
  cylinder (componentEdgeAddress address) (retainedComponentState rule marks address)

theorem componentCylinderWeight_compatible (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (cylinder : List (Fin rule.edges) → OrientedState → ℝ)
    (inactive_zero : ∀ address, cylinder address .inactive = 0)
    (both_split : ∀ address, cylinder address .both = cylinder address .sourceOnly + cylinder address .targetOnly)
    (compatible : ∀ address parent, cylinder address parent =
      ∑ edge, cylinder (address ++ [edge]) (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge)) (address : List (Fin rule.edges × Bool)) :
    componentCylinderWeight rule marks cylinder address =
      ∑ choice : Fin rule.edges × Bool, componentCylinderWeight rule marks cylinder (address ++ [choice]) := by
  simp only [componentCylinderWeight, retainedComponentState_append_singleton, componentEdgeAddress,
    List.map_append, List.map_cons, List.map_nil]
  rw [Fintype.sum_prod_type]
  simp_rw [componentChildState_mass_sum _ (inactive_zero _) (both_split _)]
  exact compatible _ _

/-- Actual component cylinders, with the two original B sides separate, are
compatible probability weights and genuine limits of retained vertex counts. -/
theorem actual_component_cylinder_probability_weights {rule : Rule} (classicalRule : rule.Classical)
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
        ∀ depth, ∑ word : Fin depth → (Fin rule.edges × Bool), weight (List.ofFn word) marks = 1 := by
  obtain ⟨cylinder, properties⟩ := compatible_retained_component_cylinder_limits classicalRule p positive below_one fixed_point
  refine ⟨fun address marks => componentCylinderWeight rule marks (fun address parent => cylinder address parent marks) address, ?_⟩
  filter_upwards [properties] with marks properties
  have inactive_zero (address : List (Fin rule.edges)) : cylinder address .inactive marks = 0 := by
    have convergence : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (cylinder address .inactive marks)) := by
      simpa only [markedOrientedVertexMass_inactive, zero_div] using (properties.2 address .inactive).2.1
    exact tendsto_nhds_unique convergence tendsto_const_nhds
  have root_one : componentCylinderWeight rule marks (fun address parent => cylinder address parent marks) [] = 1 := by
    simpa only [componentCylinderWeight, componentEdgeAddress, List.map_nil, retainedComponentState, retainedComponentStateFrom] using properties.1
  have compatibility := componentCylinderWeight_compatible rule marks (fun address parent => cylinder address parent marks) inactive_zero
    (fun address => (properties.2 address .both).2.2.2.2 rfl)
    (fun address parent => (properties.2 address parent).2.2.1)
  refine ⟨root_one, ?_, compatible_tree_weights_sum_one _ root_one compatibility⟩
  intro address
  refine ⟨(properties.2 (componentEdgeAddress address) (retainedComponentState rule marks address)).1,
    compatibility address, ?_, ?_, ?_⟩
  · simpa only [componentCylinderWeight, componentEdgeAddress, List.length_map] using
      (properties.2 (componentEdgeAddress address) (retainedComponentState rule marks address)).2.1
  · intro inactive
    exact (congrArg (cylinder (componentEdgeAddress address) · marks) inactive).trans (inactive_zero _)
  · intro connected
    rw [componentCylinderWeight, connected]
    exact (properties.2 (componentEdgeAddress address) .connected).2.2.2.1 rfl

end IGSIII.Chemical.Substitution
