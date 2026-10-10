import IGSIII.Mass.ComponentCylinderWeights

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section

open Universality Universality.FiniteNetwork Filter MeasureTheory
open scoped BigOperators Topology

/-- The actual count in one retained component of an addressed descendant. -/
def markedComponentVertexMass (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges × Bool)) : ℝ :=
  markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address)

/-- The finitely many internal vertices planted before the selected level. -/
def componentFrontierVertexMass (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    ℕ → List (Fin rule.edges × Bool) → ℝ
  | 0, _ => 0
  | age + 1, address =>
      (rule.network.internalStateMass (retainedComponentState rule marks address)
        (marks (componentEdgeAddress address, (retainedComponentState rule marks address).massOpened)) : ℝ) +
      ∑ choice : Fin rule.edges × Bool, componentFrontierVertexMass rule marks age (address ++ [choice])

theorem componentFrontierVertexMass_nonnegative (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (age : ℕ) (address : List (Fin rule.edges × Bool)) :
    0 ≤ componentFrontierVertexMass rule marks age address := by
  induction age generalizing address with
  | zero => exact le_rfl
  | succ age induction_hypothesis =>
      exact add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun choice _ => induction_hypothesis _))

theorem markedComponentVertexMass_substitute (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges × Bool)) :
    markedComponentVertexMass rule marks (depth + 1) address =
      (rule.network.internalStateMass (retainedComponentState rule marks address)
        (marks (componentEdgeAddress address, (retainedComponentState rule marks address).massOpened)) : ℝ) +
      ∑ choice : Fin rule.edges × Bool, markedComponentVertexMass rule marks depth (address ++ [choice]) := by
  rw [markedComponentVertexMass, markedOrientedVertexMass_substitute rule marks crossing]
  congr 1
  simp only [markedComponentVertexMass, retainedComponentState_append_singleton,
    componentEdgeAddress, List.map_append, List.map_cons, List.map_nil, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro edge _
  symm
  apply componentChildState_mass_sum
  · exact markedOrientedVertexMass_inactive rule marks depth _
  · exact markedOrientedVertexMass_joint_both rule marks crossing depth _

/-- At every finite depth the actual root count is the sum of the actual
single-component descendant counts and a fixed finite frontier count.
The identity uses the original joint B configuration on both sides. -/
theorem actual_component_finite_partition (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (address : List (Fin rule.edges × Bool)) :
    markedComponentVertexMass rule marks (fine + age) address =
      componentFrontierVertexMass rule marks age address +
      ∑ word : Fin age → (Fin rule.edges × Bool),
        markedComponentVertexMass rule marks fine (address ++ List.ofFn word) := by
  induction age generalizing address with
  | zero => simp [componentFrontierVertexMass]
  | succ age induction_hypothesis =>
      rw [show fine + (age + 1) = (fine + age) + 1 by omega,
        markedComponentVertexMass_substitute rule marks crossing]
      simp_rw [induction_hypothesis]
      rw [Finset.sum_add_distrib]
      change _ = (_ + _) + _
      rw [add_assoc]
      congr 1
      congr 1
      rw [← (Fin.consEquiv (fun _ : Fin (age + 1) => Fin rule.edges × Bool)).sum_comp]
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro choice _
      apply Finset.sum_congr rfl
      intro word _
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero,
        Fin.cons_succ, List.append_assoc, List.singleton_append]

theorem actual_component_level_count_le_root (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (address : List (Fin rule.edges × Bool)) :
    (∑ word : Fin age → (Fin rule.edges × Bool),
        markedComponentVertexMass rule marks fine (address ++ List.ofFn word)) ≤
      markedComponentVertexMass rule marks (fine + age) address := by
  rw [actual_component_finite_partition rule marks crossing]
  exact le_add_of_nonneg_left (componentFrontierVertexMass_nonnegative rule marks age address)

end
end IGSIII.Chemical.Substitution
