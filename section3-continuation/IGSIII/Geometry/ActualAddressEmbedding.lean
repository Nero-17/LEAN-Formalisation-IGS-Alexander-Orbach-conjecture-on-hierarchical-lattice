import IGSIII.Geometry.ActualComponentEmbedding

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- The actual finite network inside a top-down edge address. -/
def generationAddressEmbedding (rule : Rule) :
    (address : List (Fin rule.edges)) → (depth : ℕ) →
      (rule.generation depth).network.NetworkEmbedding (rule.generation (depth + address.length)).network
  | [], depth => NetworkEmbedding.refl _
  | edge :: tail, depth => by
      simpa only [List.length_cons, Nat.add_succ] using
        (generationAddressEmbedding rule tail depth).trans (rule.generationCellEmbedding (depth + tail.length) edge)

theorem retainedComponentStateFrom_inactive (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (ancestor : List (Fin rule.edges)) (address : List (Fin rule.edges × Bool)) :
    retainedComponentStateFrom rule marks ancestor .inactive address = .inactive := by
  induction address generalizing ancestor with
  | nil => rfl
  | cons choice tail induction_hypothesis =>
      simpa only [retainedComponentStateFrom, OrientedState.sourceSelected, OrientedState.targetSelected,
        orientedChildState, selectedActive, Bool.false_and, Bool.false_or, orientedStateOf,
        Bool.false_eq_true, ↓reduceIte, componentChildState] using induction_hypothesis (ancestor ++ [choice.1])

theorem retainedComponentStateFrom_live_parent (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (ancestor : List (Fin rule.edges)) (parent : OrientedState) (address : List (Fin rule.edges × Bool))
    (live : retainedComponentStateFrom rule marks ancestor parent address ≠ .inactive) : parent ≠ .inactive := by
  intro inactive
  rw [inactive, retainedComponentStateFrom_inactive] at live
  exact live rfl

/-- Actual cell embeddings preserve membership of every retained split
component all the way back to its ancestor mask. -/
theorem generationAddressEmbedding_selected_component (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (address : List (Fin rule.edges × Bool))
    (live : retainedComponentStateFrom rule marks ancestor parent address ≠ .inactive)
    (vertex : Fin (rule.generation depth).vertices)
    (selected : (rule.generation depth).network.selectedActive
      (retainedComponentStateFrom rule marks ancestor parent address).sourceSelected
      (retainedComponentStateFrom rule marks ancestor parent address).targetSelected
      (markedGenerationConfiguration rule marks depth (ancestor ++ componentEdgeAddress address)
        (retainedComponentStateFrom rule marks ancestor parent address).massOpened) vertex = true) :
    (rule.generation (depth + (componentEdgeAddress address).length)).network.selectedActive parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) ancestor parent.massOpened)
      ((generationAddressEmbedding rule (componentEdgeAddress address) depth).vertex vertex) = true := by
  induction address generalizing ancestor parent with
  | nil => simpa only [componentEdgeAddress, List.map_nil, List.append_nil, List.length_nil, Nat.add_zero,
      generationAddressEmbedding, NetworkEmbedding.refl, Function.Embedding.refl_apply, retainedComponentStateFrom] using selected
  | cons choice tail induction_hypothesis =>
      have child_live := retainedComponentStateFrom_live_parent rule marks (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) tail live
      have child_selected := induction_hypothesis (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) live (by
            simpa only [retainedComponentStateFrom, componentEdgeAddress, List.map_cons,
              List.append_assoc, List.singleton_append] using selected)
      have embedded := embedded_split_component_selected rule marks crossing (depth + (componentEdgeAddress tail).length)
        ancestor parent choice.1 choice.2 child_live _ child_selected
      simpa only [componentEdgeAddress, List.map_cons, List.length_cons, Nat.add_succ,
        Nat.add_zero, generationAddressEmbedding, NetworkEmbedding.trans, id_eq,
        Function.Embedding.trans_apply] using embedded

/-- Restricting the original ancestor configuration to a live split address
gives precisely its original marked descendant configuration. -/
theorem generationAddressEmbedding_restrict_marked_component (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (address : List (Fin rule.edges × Bool))
    (live : retainedComponentStateFrom rule marks ancestor parent address ≠ .inactive) :
    (generationAddressEmbedding rule (componentEdgeAddress address) depth).restrict
      (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) ancestor parent.massOpened) =
      markedGenerationConfiguration rule marks depth (ancestor ++ componentEdgeAddress address)
        (retainedComponentStateFrom rule marks ancestor parent address).massOpened := by
  induction address generalizing ancestor parent with
  | nil => simp only [componentEdgeAddress, List.map_nil, List.length_nil, Nat.add_zero,
      generationAddressEmbedding, NetworkEmbedding.refl, List.append_nil, retainedComponentStateFrom]
           rfl
  | cons choice tail induction_hypothesis =>
      have child_live := retainedComponentStateFrom_live_parent rule marks (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) tail live
      have bit := live_component_child_crossing_bit rule.network (marks (ancestor, parent.massOpened))
        parent.sourceSelected parent.targetSelected choice.1 choice.2 child_live
      have restriction := generationCellEmbedding_restrict_marked rule marks
        (depth + (componentEdgeAddress tail).length) ancestor parent.massOpened choice.1
      change (generationAddressEmbedding rule (componentEdgeAddress tail) depth).restrict
        ((rule.generationCellEmbedding (depth + (componentEdgeAddress tail).length) choice.1).restrict
          (markedGenerationConfiguration rule marks ((depth + (componentEdgeAddress tail).length) + 1) ancestor parent.massOpened)) = _
      rw [restriction, ← bit]
      simpa only [componentEdgeAddress, List.map_cons, List.append_assoc, List.singleton_append,
        retainedComponentStateFrom] using induction_hypothesis (ancestor ++ [choice.1])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) choice.1) choice.2) live

end
end IGSIII.Geometry
