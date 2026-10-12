import IGSIII34.Spectral.ActualCollarMassBoundCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory Filter Matrix IGSIII.Geometry
open scoped BigOperators

theorem oriented_child_joint_mass_completion {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (noncrossing : network.crosses configuration = false)
    (edge : Fin edges) (mass : OrientedState → ℝ)
    (inactiveZero : mass .inactive = 0)
    (bothSplit : mass .both = mass .sourceOnly + mass .targetOnly) :
    mass (network.orientedChildState true true configuration edge) =
      mass (network.orientedChildState true false configuration edge) +
        mass (network.orientedChildState false true configuration edge) := by
  have firstDisjoint := network.source_target_disjoint_of_disconnected configuration noncrossing (network.endpoint edge).1
  have lastDisjoint := network.source_target_disjoint_of_disconnected configuration noncrossing (network.endpoint edge).2
  have sourceOpen : configuration edge = true →
      (network.openGraph configuration).reachableDecide network.source (network.endpoint edge).1 =
        (network.openGraph configuration).reachableDecide network.source (network.endpoint edge).2 := by
    intro opened
    simpa only [selectedActive, Bool.true_and, Bool.false_and, Bool.or_false] using
      network.selectedActive_endpoints_eq_of_open true false configuration edge opened
  have targetOpen : configuration edge = true →
      (network.openGraph configuration).reachableDecide network.target (network.endpoint edge).1 =
        (network.openGraph configuration).reachableDecide network.target (network.endpoint edge).2 := by
    intro opened
    simpa only [selectedActive, Bool.true_and, Bool.false_and, Bool.false_or] using
      network.selectedActive_endpoints_eq_of_open false true configuration edge opened
  cases firstSource : (network.openGraph configuration).reachableDecide network.source (network.endpoint edge).1 <;>
    cases lastSource : (network.openGraph configuration).reachableDecide network.source (network.endpoint edge).2 <;>
    cases firstTarget : (network.openGraph configuration).reachableDecide network.target (network.endpoint edge).1 <;>
    cases lastTarget : (network.openGraph configuration).reachableDecide network.target (network.endpoint edge).2 <;>
    cases opened : configuration edge <;>
    simp only [orientedChildState, selectedActive, orientedStateOf, firstSource, lastSource,
      firstTarget, lastTarget, opened, Bool.true_and, Bool.false_and,
      Bool.or_true, Bool.or_false, add_comm] <;> simp_all

def socketMaskResponseCompletion (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → OrientedState → ℝ) :
    List (Fin rule.edges) → OrientedState → List (Fin rule.edges) → ℝ
  | ancestor, parent, [] => field ancestor parent
  | ancestor, parent, edge :: tail => socketMaskResponseCompletion rule marks field
      (ancestor ++ [edge])
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (ancestor, parent.massOpened)) edge) tail

theorem socketMaskResponse_inactive_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → OrientedState → ℝ)
    (inactiveZero : ∀ address, field address .inactive = 0)
    (ancestor tail : List (Fin rule.edges)) :
    socketMaskResponseCompletion rule marks field ancestor .inactive tail = 0 := by
  induction tail generalizing ancestor with
  | nil => exact inactiveZero ancestor
  | cons edge tail inductionHypothesis =>
    simp only [socketMaskResponseCompletion, OrientedState.sourceSelected, OrientedState.targetSelected,
      orientedChildState, selectedActive, Bool.false_and, Bool.false_or, orientedStateOf]
    exact inductionHypothesis _

theorem socketMaskResponse_joint_both_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (field : List (Fin rule.edges) → OrientedState → ℝ)
    (inactiveZero : ∀ address, field address .inactive = 0)
    (bothSplit : ∀ address, field address .both = field address .sourceOnly + field address .targetOnly)
    (ancestor tail : List (Fin rule.edges)) :
    socketMaskResponseCompletion rule marks field ancestor .both tail =
      socketMaskResponseCompletion rule marks field ancestor .sourceOnly tail +
        socketMaskResponseCompletion rule marks field ancestor .targetOnly tail := by
  induction tail generalizing ancestor with
  | nil => exact bothSplit ancestor
  | cons edge tail inductionHypothesis =>
    simp only [socketMaskResponseCompletion, OrientedState.sourceSelected,
      OrientedState.targetSelected, OrientedState.massOpened]
    exact oriented_child_joint_mass_completion rule.network (marks (ancestor, false))
      (crossing ancestor false) edge
      (fun parent => socketMaskResponseCompletion rule marks field (ancestor ++ [edge]) parent tail)
      (socketMaskResponse_inactive_completion rule marks field inactiveZero _ _)
      (inductionHypothesis _)

/-- Summing component-side words at one physical socket preserves the
original joint mask. In particular the number of branch choices does not
produce an artificial factor 2^n. -/
theorem grouped_component_socket_mass_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (field : List (Fin rule.edges) → OrientedState → ℝ)
    (inactiveZero : ∀ address, field address .inactive = 0)
    (bothSplit : ∀ address, field address .both = field address .sourceOnly + field address .targetOnly)
    (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (edges : Fin depth → Fin rule.edges) :
    (∑ sides : Fin depth → Bool,
      field (ancestor ++ List.ofFn edges)
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn (fun index => (edges index, sides index))))) =
      socketMaskResponseCompletion rule marks field ancestor parent (List.ofFn edges) := by
  classical
  induction depth generalizing ancestor parent with
  | zero => simp [socketMaskResponseCompletion, retainedComponentStateFrom]
  | succ depth inductionHypothesis =>
    rw [← (Fin.consEquiv (fun _ : Fin (depth + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      retainedComponentStateFrom, socketMaskResponseCompletion]
    have regroup (side : Bool) :
        (∑ sides : Fin depth → Bool,
          field (ancestor ++ edges 0 :: List.ofFn (fun index => edges index.succ))
            (retainedComponentStateFrom rule marks (ancestor ++ [edges 0])
              (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
                (marks (ancestor, parent.massOpened)) (edges 0)) side)
              (List.ofFn (fun index => (edges index.succ, sides index))))) =
        socketMaskResponseCompletion rule marks field (ancestor ++ [edges 0])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) (edges 0)) side)
          (List.ofFn (fun index => edges index.succ)) := by
      simpa only [List.append_assoc, List.singleton_append] using inductionHypothesis
        (ancestor ++ [edges 0]) _ (fun index => edges index.succ)
    simp_rw [regroup]
    exact componentChildState_mass_sum
      (fun state => socketMaskResponseCompletion rule marks field (ancestor ++ [edges 0]) state
        (List.ofFn (fun index => edges index.succ)))
      (socketMaskResponse_inactive_completion rule marks field inactiveZero _ _)
      (socketMaskResponse_joint_both_completion rule marks crossing field inactiveZero bothSplit _ _) _

theorem socketMaskResponse_le_field_sum_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → OrientedState → ℝ)
    (nonnegative : ∀ address parent, 0 ≤ field address parent)
    (ancestor : List (Fin rule.edges)) (parent : OrientedState) (tail : List (Fin rule.edges)) :
    socketMaskResponseCompletion rule marks field ancestor parent tail ≤
      ∑ state : OrientedState, field (ancestor ++ tail) state := by
  induction tail generalizing ancestor parent with
  | nil =>
    simp only [socketMaskResponseCompletion, List.append_nil]
    exact Finset.single_le_sum (fun state _ => nonnegative ancestor state) (Finset.mem_univ parent)
  | cons edge tail inductionHypothesis =>
    simpa only [socketMaskResponseCompletion, List.append_assoc, List.singleton_append]
      using inductionHypothesis (ancestor ++ [edge])
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) edge)

/-- On the actual joint mass field, all component-side words addressing
one physical descendant socket have uniformly bounded total continuation
mass. The bound has five original mask terms, independently of depth. -/
theorem actual_grouped_component_socket_mass_bound_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
        (edges : Fin depth → Fin rule.edges),
      (∑ sides : Fin depth → Bool,
        continuation.mass
          (retainedComponentStateFrom rule marks ancestor parent (List.ofFn (fun index => (edges index, sides index))))
          (innovationTreeShift rule (ancestor ++ List.ofFn edges) marks)) ≤
      ∑ state : OrientedState, continuation.mass state
        (innovationTreeShift rule (ancestor ++ List.ofFn edges) marks) := by
  have inactive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, continuation.mass .inactive (innovationTreeShift rule address marks) = 0 := by
    apply ae_all_iff.mpr
    intro address
    exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae continuation.inactive
  have joint : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, continuation.mass .both (innovationTreeShift rule address marks) =
        continuation.mass .sourceOnly (innovationTreeShift rule address marks) +
          continuation.mass .targetOnly (innovationTreeShift rule address marks) := by
    apply ae_all_iff.mpr
    intro address
    exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae continuation.jointBoth
  filter_upwards [inactive, joint, independentInnovationLaw_crosses rule p positive belowOne fixedPoint]
    with marks inactive joint crossing
  intro depth ancestor parent edges
  let field := fun address state => continuation.mass state (innovationTreeShift rule address marks)
  rw [grouped_component_socket_mass_completion rule marks crossing field inactive joint]
  exact socketMaskResponse_le_field_sum_completion rule marks field
    (fun _ state => continuation.nonnegative state _) ancestor parent (List.ofFn edges)

end
end IGSIII34.Spectral
