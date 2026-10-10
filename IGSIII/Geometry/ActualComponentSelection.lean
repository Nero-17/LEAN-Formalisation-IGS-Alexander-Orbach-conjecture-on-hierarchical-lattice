import IGSIII.Geometry.ActualSkeletonVertices
import IGSIII.Geometry.RetainedComponentDiameter
import IGSIII.Mass.ComponentCylinderWeights

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open scoped BigOperators

variable {vertices edges : ℕ}

/-- A live state after B has been split selects precisely one actual connected
component, planted at its selected source or target. -/
theorem single_oriented_component_selected_iff (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (parent : OrientedState)
    (not_both : parent ≠ .both) (not_inactive : parent ≠ .inactive)
    (crossing : network.crosses configuration = parent.massOpened) (vertex : Fin vertices) :
    network.selectedActive parent.sourceSelected parent.targetSelected configuration vertex = true ↔
      (network.openGraph configuration).Reachable (plantedVertex network parent.sourceSelected) vertex := by
  cases parent with
  | connected =>
      have terminal_reachable : (network.openGraph configuration).Reachable network.source network.target :=
        (network.crosses_eq_true configuration).mp crossing
      simp only [OrientedState.sourceSelected, OrientedState.targetSelected, plantedVertex,
        ↓reduceIte, selectedActive, Bool.true_and, Bool.or_eq_true,
        SimpleGraph.reachableDecide_eq_true]
      exact ⟨fun selected => selected.elim id (fun reachable => terminal_reachable.trans reachable), Or.inl⟩
  | both => exact (not_both rfl).elim
  | sourceOnly =>
      simp only [OrientedState.sourceSelected, OrientedState.targetSelected, plantedVertex,
        ↓reduceIte, selectedActive, Bool.true_and, Bool.false_and, Bool.or_false,
        SimpleGraph.reachableDecide_eq_true]
  | targetOnly =>
      simp only [OrientedState.sourceSelected, OrientedState.targetSelected, plantedVertex,
        Bool.false_eq_true, ↓reduceIte, selectedActive, Bool.false_and, Bool.true_and, Bool.false_or,
        SimpleGraph.reachableDecide_eq_true]
  | inactive => exact (not_inactive rfl).elim

theorem split_component_selection_implies_original (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (parent : OrientedState) (side : Bool) (vertex : Fin vertices)
    (selected : network.selectedActive (componentChildState parent side).sourceSelected
      (componentChildState parent side).targetSelected configuration vertex = true) :
    network.selectedActive parent.sourceSelected parent.targetSelected configuration vertex = true := by
  cases parent <;> cases side <;>
    simp_all [componentChildState, OrientedState.sourceSelected, OrientedState.targetSelected,
      selectedActive, Bool.or_eq_true]

theorem marked_component_selected_iff (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks address ≠ .inactive)
    (vertex : Fin (rule.generation depth).vertices) :
    (rule.generation depth).network.selectedActive (retainedComponentState rule marks address).sourceSelected
        (retainedComponentState rule marks address).targetSelected
        (markedGenerationConfiguration rule marks depth (componentEdgeAddress address)
          (retainedComponentState rule marks address).massOpened) vertex = true ↔
      ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth
        (componentEdgeAddress address) (retainedComponentState rule marks address).massOpened)).Reachable
          (plantedVertex (rule.generation depth).network (retainedComponentState rule marks address).sourceSelected) vertex :=
  single_oriented_component_selected_iff (rule.generation depth).network _ _
    (retainedComponentState_ne_both rule marks address) live
    (markedGenerationConfiguration_crosses rule marks crossing depth _ _) vertex

/-- The sampled component count is literally its selected internal vertex
cardinality in the original microscopic configuration. -/
theorem marked_component_internal_count_eq (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks address ≠ .inactive) :
    markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) =
      ∑ vertex : (rule.generation depth).network.InteriorVertex,
        if ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth
          (componentEdgeAddress address) (retainedComponentState rule marks address).massOpened)).Reachable
            (plantedVertex (rule.generation depth).network (retainedComponentState rule marks address).sourceSelected) vertex.val
        then (1 : ℝ) else 0 := by
  simp only [markedOrientedVertexMass, internalStateMass, internalSelectedMass, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro vertex _
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    marked_component_selected_iff rule marks crossing depth address live]

theorem marked_single_component_diameter_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks address ≠ .inactive)
    (first last : Fin (rule.generation depth).vertices)
    (selected_first : (rule.generation depth).network.selectedActive (retainedComponentState rule marks address).sourceSelected
      (retainedComponentState rule marks address).targetSelected (markedGenerationConfiguration rule marks depth
        (componentEdgeAddress address) (retainedComponentState rule marks address).massOpened) first = true)
    (selected_last : (rule.generation depth).network.selectedActive (retainedComponentState rule marks address).sourceSelected
      (retainedComponentState rule marks address).targetSelected (markedGenerationConfiguration rule marks depth
        (componentEdgeAddress address) (retainedComponentState rule marks address).massOpened) last = true) :
    ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth
      (componentEdgeAddress address) (retainedComponentState rule marks address).massOpened)).dist first last ≤
        2 * markedTerminalComponentRadius rule marks depth (componentEdgeAddress address)
          (retainedComponentState rule marks address).massOpened := by
  apply selected_component_distance_le_twice_radius _ _ _ _ _ _ selected_first
  exact ((marked_component_selected_iff rule marks crossing depth address live first).mp selected_first).symm.trans
    ((marked_component_selected_iff rule marks crossing depth address live last).mp selected_last)

end
end IGSIII.Geometry
