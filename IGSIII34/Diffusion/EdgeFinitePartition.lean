import IGSIII34.Diffusion.ComponentEdgeLimits
import IGSIII.Geometry.ConnectedComponentWords

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem markedOrientedEdgeMass_inactive (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    markedOrientedEdgeMass rule marks depth address .inactive = 0 :=
  orientedEdgeReward_inactive _ _

theorem markedOrientedEdgeMass_joint_both (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    markedOrientedEdgeMass rule marks depth address .both =
      markedOrientedEdgeMass rule marks depth address .sourceOnly +
      markedOrientedEdgeMass rule marks depth address .targetOnly :=
  orientedEdgeReward_joint_both _ _ (markedGenerationConfiguration_crosses rule marks crossing depth address false)

/-- Retained edges belong to descendants exactly: unlike vertex rewards, no
older planting vertex contributes a frontier correction. -/
theorem markedOrientedEdgeMass_substitute (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    markedOrientedEdgeMass rule marks (depth + 1) address parent =
      ∑ edge, markedOrientedEdgeMass rule marks depth (address ++ [edge])
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (address, parent.massOpened)) edge) := by
  classical
  unfold markedOrientedEdgeMass orientedEdgeReward orientedLiveCount
  push_cast
  rw [← (finProdFinEquiv.trans (rule.generationTopDecomposition depth).edge.symm).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases inactive : rule.network.orientedChildState parent.sourceSelected parent.targetSelected
      (marks (address, parent.massOpened)) edge = .inactive
  · apply Finset.sum_congr rfl
    intro child _
    change (if (rule.generation (depth + 1)).network.orientedChildState parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened)
      ((rule.generationCellEmbedding depth edge).edge child) = OrientedState.connected then (1 : ℝ) else 0) = _
    rw [marked_orientedChildState_top rule marks crossing, inactive]
    simp [inactive, OrientedState.sourceSelected, OrientedState.targetSelected,
      orientedChildState, selectedActive, orientedStateOf]
  · have bit : (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge).massOpened = marks (address, parent.massOpened) edge := by
      apply Bool.eq_iff_iff.mpr
      simp only [OrientedState.massOpened, decide_eq_true_eq]
      exact rule.network.live_oriented_state_determines_crossing parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge inactive
    rw [bit]
    apply Finset.sum_congr rfl
    intro child _
    change (if (rule.generation (depth + 1)).network.orientedChildState parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened)
      ((rule.generationCellEmbedding depth edge).edge child) = OrientedState.connected then (1 : ℝ) else 0) = _
    rw [marked_orientedChildState_top rule marks crossing]

theorem markedComponentEdgeMass_substitute (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges × Bool)) :
    markedComponentEdgeMass rule marks (depth + 1) address =
      ∑ choice : Fin rule.edges × Bool, markedComponentEdgeMass rule marks depth (address ++ [choice]) := by
  rw [markedComponentEdgeMass, markedOrientedEdgeMass_substitute rule marks crossing]
  simp only [markedComponentEdgeMass, retainedComponentState_append_singleton,
    componentEdgeAddress, List.map_append, List.map_cons, List.map_nil, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro edge _
  symm
  apply componentChildState_mass_sum
  · exact markedOrientedEdgeMass_inactive rule marks depth _
  · exact markedOrientedEdgeMass_joint_both rule marks crossing depth _

theorem actual_component_edge_finite_partition (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (address : List (Fin rule.edges × Bool)) :
    markedComponentEdgeMass rule marks (fine + age) address =
      ∑ word : Fin age → (Fin rule.edges × Bool),
        markedComponentEdgeMass rule marks fine (address ++ List.ofFn word) := by
  induction age generalizing address with
  | zero => simp
  | succ age induction_hypothesis =>
      rw [show fine + (age + 1) = (fine + age) + 1 by omega,
        markedComponentEdgeMass_substitute rule marks crossing]
      simp_rw [induction_hypothesis]
      rw [← (Fin.consEquiv (fun _ : Fin (age + 1) => Fin rule.edges × Bool)).sum_comp]
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro choice _
      apply Finset.sum_congr rfl
      intro word _
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero,
        Fin.cons_succ, List.append_assoc, List.singleton_append]

end
end IGSIII34.Diffusion
