import IGSIII.Geometry.ComponentWordAnchors

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- A connected descendant edge lies in exactly one of the two original
components when a B mask is split. Existence suffices here. -/
theorem connected_edge_has_split_component {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (parent : OrientedState) (edge : Fin edges)
    (connected : network.orientedChildState parent.sourceSelected parent.targetSelected configuration edge = .connected) :
    ∃ side : Bool, network.orientedChildState (componentChildState parent side).sourceSelected
      (componentChildState parent side).targetSelected configuration edge = .connected := by
  have selected := (network.orientedChildState_connected_iff _ _ _ _).mp connected
  cases parent with
  | connected => exact ⟨true, connected⟩
  | sourceOnly => exact ⟨true, connected⟩
  | targetOnly => exact ⟨false, connected⟩
  | inactive => simp [OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive] at selected
  | both =>
    have either : (network.openGraph configuration).Reachable network.source (network.endpoint edge).1 ∨
        (network.openGraph configuration).Reachable network.target (network.endpoint edge).1 := by
      simpa only [OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive,
        Bool.true_and, Bool.or_eq_true, SimpleGraph.reachableDecide_eq_true] using selected.2
    rcases either with source_reachable | target_reachable
    · refine ⟨true, (network.orientedChildState_connected_iff _ _ _ _).mpr ⟨selected.1, ?_⟩⟩
      simpa only [componentChildState, OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive,
        Bool.true_and, Bool.false_and, Bool.or_false, SimpleGraph.reachableDecide_eq_true] using source_reachable
    · refine ⟨false, (network.orientedChildState_connected_iff _ _ _ _).mpr ⟨selected.1, ?_⟩⟩
      simpa only [componentChildState, OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive,
        Bool.true_and, Bool.false_and, Bool.false_or, SimpleGraph.reachableDecide_eq_true] using target_reachable

theorem marked_orientedChildState_top (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) :
    (rule.generation (depth + 1)).network.orientedChildState parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + 1) ancestor parent.massOpened)
      ((rule.generationCellEmbedding depth edge).edge child) =
      (rule.generation depth).network.orientedChildState
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (ancestor, parent.massOpened)) edge).sourceSelected
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (ancestor, parent.massOpened)) edge).targetSelected
        (markedGenerationConfiguration rule marks depth (ancestor ++ [edge]) (marks (ancestor, parent.massOpened) edge)) child := by
  simp only [orientedChildState, rule.generationCellEmbedding_endpoint]
  rw [generationCellEmbedding_selectedActive_marked rule marks crossing,
    generationCellEmbedding_selectedActive_marked rule marks crossing]
  congr 1
  exact markedGenerationConfiguration_top_apply rule marks depth ancestor parent.massOpened edge child

/-- Every actual retained open edge has a genuine single-component word,
including edges reached through an original B socket. -/
theorem exists_connected_component_word (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (edge : Fin (rule.generation depth).edges)
    (connected : (rule.generation depth).network.orientedChildState parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks depth ancestor parent.massOpened) edge = .connected) :
    ∃ word : Fin (depth + 1) → (Fin rule.edges × Bool),
      generationWordEdge rule depth (fun index => (word index).1) = edge ∧
      retainedComponentStateFrom rule marks ancestor parent (List.ofFn word) = .connected := by
  induction depth generalizing ancestor parent with
  | zero =>
    change rule.network.orientedChildState parent.sourceSelected parent.targetSelected
      (marks (ancestor, parent.massOpened)) edge = .connected at connected
    refine ⟨fun _ => (edge, true), rfl, ?_⟩
    simp only [List.ofFn_succ, List.ofFn_zero, retainedComponentStateFrom, connected, componentChildState]
  | succ depth induction_hypothesis =>
    let pair := finProdFinEquiv.symm ((rule.generationTopDecomposition depth).edge edge)
    have edge_identity : edge = (rule.generationCellEmbedding depth pair.1).edge pair.2 := by
      change edge = (rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (pair.1, pair.2))
      simp only [pair, Prod.eta, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rw [edge_identity, marked_orientedChildState_top rule marks crossing] at connected
    obtain ⟨side, split_connected⟩ := connected_edge_has_split_component (rule.generation depth).network _
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (ancestor, parent.massOpened)) pair.1) pair.2 connected
    have child_live : componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (ancestor, parent.massOpened)) pair.1) side ≠ .inactive := by
      intro inactive
      rw [inactive] at split_connected
      simp [orientedChildState, OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive, orientedStateOf] at split_connected
    have bit := live_component_child_crossing_bit rule.network _ _ _ _ _ child_live
    rw [← bit] at split_connected
    obtain ⟨tail, tail_edge, tail_state⟩ := induction_hypothesis (ancestor ++ [pair.1]) _ pair.2 split_connected
    refine ⟨Fin.cons (pair.1, side) tail, ?_, ?_⟩
    · rw [generationWordEdge]
      simp only [Fin.cons_zero, Fin.cons_succ, tail_edge]
      change edge = (rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (pair.1, pair.2)) at edge_identity
      exact edge_identity.symm
    · simpa only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, retainedComponentStateFrom] using tail_state

end
end IGSIII.Geometry
