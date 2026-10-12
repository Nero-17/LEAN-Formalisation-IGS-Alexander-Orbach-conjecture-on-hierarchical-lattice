import IGSIII34.Diffusion.EdgeFinitePartition
import IGSIII.Mass.ThreeStateMassPerron
import Universality.Percolation.StateRowIdentities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace IGSIII34.Spectral
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

/-- A closed socket can retain both original sides, which count separately. -/
def componentSlotCountCompletion : OrientedState → ℝ
  | .inactive => 0
  | .both => 2
  | _ => 1

def componentSlotResponseCompletion {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (parent : OrientedState) : ℝ :=
  ∑ edge, componentSlotCountCompletion
    (network.orientedChildState parent.sourceSelected parent.targetSelected configuration edge)

theorem componentSlotResponse_nonnegative_completion {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (parent : OrientedState) : 0 ≤ componentSlotResponseCompletion network configuration parent := by
  apply Finset.sum_nonneg
  intro edge _
  cases network.orientedChildState parent.sourceSelected parent.targetSelected configuration edge <;>
    norm_num [componentSlotCountCompletion]

theorem componentSlotResponse_inactive_completion {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges) :
    componentSlotResponseCompletion network configuration .inactive = 0 := by
  simp [componentSlotResponseCompletion, OrientedState.sourceSelected,
    OrientedState.targetSelected, orientedChildState, selectedActive, orientedStateOf,
    componentSlotCountCompletion]

theorem componentSlotResponse_joint_both_completion {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (noncrossing : network.crosses configuration = false) :
    componentSlotResponseCompletion network configuration .both =
      componentSlotResponseCompletion network configuration .sourceOnly +
        componentSlotResponseCompletion network configuration .targetOnly := by
  unfold componentSlotResponseCompletion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  have firstDisjoint := network.source_target_disjoint_of_disconnected configuration noncrossing
    (network.endpoint edge).1
  have lastDisjoint := network.source_target_disjoint_of_disconnected configuration noncrossing
    (network.endpoint edge).2
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
    norm_num [orientedChildState, selectedActive, orientedStateOf, OrientedState.sourceSelected,
      OrientedState.targetSelected, componentSlotCountCompletion, firstSource, lastSource,
      firstTarget, lastTarget, opened] <;> simp_all

def markedComponentSlotResponseCompletion (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) : ℝ :=
  componentSlotResponseCompletion (rule.generation depth).network
    (markedGenerationConfiguration rule marks depth address parent.massOpened) parent

theorem markedComponentSlotResponse_substitute_completion (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    markedComponentSlotResponseCompletion rule marks (depth + 1) address parent =
      ∑ edge, markedComponentSlotResponseCompletion rule marks depth (address ++ [edge])
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (address, parent.massOpened)) edge) := by
  classical
  unfold markedComponentSlotResponseCompletion componentSlotResponseCompletion
  rw [← (finProdFinEquiv.trans (rule.generationTopDecomposition depth).edge.symm).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases inactive : rule.network.orientedChildState parent.sourceSelected parent.targetSelected
      (marks (address, parent.massOpened)) edge = .inactive
  · apply Finset.sum_congr rfl
    intro child _
    change componentSlotCountCompletion
      ((rule.generation (depth + 1)).network.orientedChildState parent.sourceSelected parent.targetSelected
        (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened)
        ((rule.generationCellEmbedding depth edge).edge child)) = _
    rw [marked_orientedChildState_top rule marks crossing, inactive]
    simp [inactive, OrientedState.sourceSelected, OrientedState.targetSelected,
      orientedChildState, selectedActive, orientedStateOf, componentSlotCountCompletion]
  · have bit : (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge).massOpened = marks (address, parent.massOpened) edge := by
      apply Bool.eq_iff_iff.mpr
      simp only [OrientedState.massOpened, decide_eq_true_eq]
      exact rule.network.live_oriented_state_determines_crossing parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge inactive
    rw [bit]
    apply Finset.sum_congr rfl
    intro child _
    change componentSlotCountCompletion
      ((rule.generation (depth + 1)).network.orientedChildState parent.sourceSelected parent.targetSelected
        (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened)
        ((rule.generationCellEmbedding depth edge).edge child)) = _
    rw [marked_orientedChildState_top rule marks crossing]

def retainedComponentSlotResponseCompletion (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges × Bool)) : ℝ :=
  markedComponentSlotResponseCompletion rule marks depth
    (componentEdgeAddress address) (retainedComponentState rule marks address)

theorem retainedComponentSlotResponse_substitute_completion (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges × Bool)) :
    retainedComponentSlotResponseCompletion rule marks (depth + 1) address =
      ∑ choice : Fin rule.edges × Bool,
        retainedComponentSlotResponseCompletion rule marks depth (address ++ [choice]) := by
  rw [retainedComponentSlotResponseCompletion,
    markedComponentSlotResponse_substitute_completion rule marks crossing]
  simp only [retainedComponentSlotResponseCompletion,
    retainedComponentState_append_singleton, componentEdgeAddress,
    List.map_append, List.map_cons, List.map_nil, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro edge _
  symm
  apply componentChildState_mass_sum
  · exact componentSlotResponse_inactive_completion _ _
  · exact componentSlotResponse_joint_both_completion _ _
      (markedGenerationConfiguration_crosses rule marks crossing depth _ false)

theorem retainedComponentSlotResponse_partition_completion (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (address : List (Fin rule.edges × Bool)) :
    retainedComponentSlotResponseCompletion rule marks (fine + age) address =
      ∑ word : Fin age → (Fin rule.edges × Bool),
        retainedComponentSlotResponseCompletion rule marks fine (address ++ List.ofFn word) := by
  induction age generalizing address with
  | zero => simp
  | succ age inductionHypothesis =>
      rw [show fine + (age + 1) = (fine + age) + 1 by omega,
        retainedComponentSlotResponse_substitute_completion rule marks crossing]
      simp_rw [inductionHypothesis]
      rw [← (Fin.consEquiv (fun _ : Fin (age + 1) => Fin rule.edges × Bool)).sum_comp]
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro choice _
      apply Finset.sum_congr rfl
      intro word _
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero,
        Fin.cons_succ, List.append_assoc, List.singleton_append]

end
end IGSIII34.Spectral
