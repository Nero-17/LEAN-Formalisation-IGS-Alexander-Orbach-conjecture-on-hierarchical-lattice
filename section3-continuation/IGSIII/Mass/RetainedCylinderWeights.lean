import IGSIII.Mass.CompatibleCylinders
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter
open scoped BigOperators Topology

/-- Follow the original joint terminal masks along an actual address. -/
def retainedAddressStateFrom (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    List (Fin rule.edges) → OrientedState → List (Fin rule.edges) → OrientedState
  | _, parent, [] => parent
  | ancestor, parent, edge :: tail => retainedAddressStateFrom rule marks (ancestor ++ [edge])
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (ancestor, parent.massOpened)) edge) tail

def retainedAddressState (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (address : List (Fin rule.edges)) : OrientedState :=
  retainedAddressStateFrom rule marks [] .connected address

theorem retainedAddressStateFrom_append (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (ancestor : List (Fin rule.edges)) (parent : OrientedState) (first second : List (Fin rule.edges)) :
    retainedAddressStateFrom rule marks ancestor parent (first ++ second) =
      retainedAddressStateFrom rule marks (ancestor ++ first) (retainedAddressStateFrom rule marks ancestor parent first) second := by
  induction first generalizing ancestor parent with
  | nil => simp only [List.nil_append, List.append_nil, retainedAddressStateFrom]
  | cons edge tail induction_hypothesis =>
    simp only [List.cons_append, retainedAddressStateFrom]
    rw [induction_hypothesis]
    simp only [List.append_assoc, List.singleton_append]

theorem retainedAddressState_nil (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    retainedAddressState rule marks [] = .connected := rfl

theorem retainedAddressState_append_singleton (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (edge : Fin rule.edges) :
    retainedAddressState rule marks (address ++ [edge]) =
      rule.network.orientedChildState (retainedAddressState rule marks address).sourceSelected
        (retainedAddressState rule marks address).targetSelected
        (marks (address, (retainedAddressState rule marks address).massOpened)) edge := by
  rw [retainedAddressState, retainedAddressStateFrom_append]
  simp only [List.nil_append, retainedAddressStateFrom, retainedAddressState]

def retainedCylinderWeight (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (cylinder : List (Fin rule.edges) → OrientedState → ℝ) (address : List (Fin rule.edges)) : ℝ :=
  cylinder address (retainedAddressState rule marks address)

theorem retainedCylinderWeight_compatible (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (cylinder : List (Fin rule.edges) → OrientedState → ℝ)
    (compatible : ∀ address parent, cylinder address parent =
      ∑ edge, cylinder (address ++ [edge]) (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge)) (address : List (Fin rule.edges)) :
    retainedCylinderWeight rule marks cylinder address =
      ∑ edge, retainedCylinderWeight rule marks cylinder (address ++ [edge]) := by
  simp only [retainedCylinderWeight, retainedAddressState_append_singleton]
  exact compatible address (retainedAddressState rule marks address)

theorem retainedCylinderWeight_nonnegative (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (cylinder : List (Fin rule.edges) → OrientedState → ℝ)
    (nonnegative : ∀ address parent, 0 ≤ cylinder address parent) (address : List (Fin rule.edges)) :
    0 ≤ retainedCylinderWeight rule marks cylinder address := nonnegative _ _

theorem compatible_tree_weights_sum_one {Alphabet : Type*} [Fintype Alphabet]
    (weight : List Alphabet → ℝ) (root_one : weight [] = 1)
    (compatible : ∀ address, weight address = ∑ edge, weight (address ++ [edge])) :
    ∀ depth, ∑ word : Fin depth → Alphabet, weight (List.ofFn word) = 1 := by
  intro depth
  induction depth with
  | zero => simpa using root_one
  | succ depth induction_hypothesis =>
    calc
      _ = ∑ pair : Alphabet × (Fin depth → Alphabet), weight (List.ofFn (Fin.snoc pair.2 pair.1)) :=
        ((Fin.snocEquiv (fun _ : Fin (depth + 1) => Alphabet)).sum_comp (fun word => weight (List.ofFn word))).symm
      _ = ∑ word : Fin depth → Alphabet, ∑ edge : Alphabet, weight (List.ofFn word ++ [edge]) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp only [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
      _ = ∑ word : Fin depth → Alphabet, weight (List.ofFn word) := by
        apply Finset.sum_congr rfl
        intro word _
        exact (compatible _).symm
      _ = 1 := induction_hypothesis

/-- The actual retained address weights form a probability distribution on
each finite level, and are the limits of the original jointly masked counts. -/
theorem actual_retained_cylinder_probability_weights {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
        weight [] marks = 1 ∧
        (∀ address, 0 ≤ weight address marks ∧
          weight address marks = ∑ edge, weight (address ++ [edge]) marks ∧
          Tendsto (fun n => markedOrientedVertexMass rule marks n address (retainedAddressState rule marks address) /
            markedOrientedVertexMass rule marks (n + address.length) [] .connected) atTop (𝓝 (weight address marks))) ∧
        ∀ depth, ∑ word : Fin depth → Fin rule.edges, weight (List.ofFn word) marks = 1 := by
  obtain ⟨cylinder, properties⟩ := compatible_retained_component_cylinder_limits classicalRule p positive below_one fixed_point
  refine ⟨fun address marks => retainedCylinderWeight rule marks (fun address parent => cylinder address parent marks) address, ?_⟩
  filter_upwards [properties] with marks properties
  have root_one : retainedCylinderWeight rule marks (fun address parent => cylinder address parent marks) [] = 1 := by
    simpa only [retainedCylinderWeight, retainedAddressState_nil] using properties.1
  have compatibility := retainedCylinderWeight_compatible rule marks (fun address parent => cylinder address parent marks)
    (fun address parent => (properties.2 address parent).2.2.1)
  refine ⟨root_one, ?_, compatible_tree_weights_sum_one _ root_one compatibility⟩
  intro address
  exact ⟨(properties.2 address (retainedAddressState rule marks address)).1, compatibility address,
    (properties.2 address (retainedAddressState rule marks address)).2.1⟩

end IGSIII.Chemical.Substitution
