import IGSIII.Geometry.ActualAddressEmbedding
import IGSIII.Mass.ComponentEmpiricalLaw
import Universality.Graph.AncestralInterior

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open scoped BigOperators

theorem noncrossing_terminal_reachable_disjoint {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (noncrossing : network.crosses configuration = false) (vertex : Fin vertices)
    (sourceReachable : (network.openGraph configuration).Reachable network.source vertex)
    (targetReachable : (network.openGraph configuration).Reachable network.target vertex) : False := by
  have connected := sourceReachable.trans targetReachable.symm
  have crossing := (network.crosses_eq_true configuration).mpr connected
  rw [noncrossing] at crossing
  exact Bool.false_ne_true crossing

theorem componentChildState_selected_unique {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (parent : OrientedState) (crossing : network.crosses configuration = parent.massOpened)
    (first last : Bool) (vertex : Fin vertices)
    (selectedFirst : network.selectedActive (componentChildState parent first).sourceSelected
      (componentChildState parent first).targetSelected configuration vertex = true)
    (selectedLast : network.selectedActive (componentChildState parent last).sourceSelected
      (componentChildState parent last).targetSelected configuration vertex = true) : first = last := by
  cases parent <;> cases first <;> cases last <;>
    simp_all [componentChildState, OrientedState.sourceSelected, OrientedState.targetSelected,
      OrientedState.massOpened, selectedActive, SimpleGraph.reachableDecide_eq_true]
  · exact (noncrossing_terminal_reachable_disjoint network configuration crossing vertex selectedLast selectedFirst).elim
  · exact (noncrossing_terminal_reachable_disjoint network configuration crossing vertex selectedFirst selectedLast).elim

def SelectedComponentInterior (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :=
  {vertex : (rule.generation depth).network.InteriorVertex //
    (rule.generation depth).network.selectedActive parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks depth address parent.massOpened) vertex.val = true}

instance selectedComponentInterior_fintype (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    Fintype (SelectedComponentInterior rule marks depth address parent) := by
  classical
  unfold SelectedComponentInterior
  infer_instance

theorem selectedComponentInterior_live (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState)
    (vertex : SelectedComponentInterior rule marks depth address parent) : parent ≠ .inactive := by
  intro inactive
  have selected := vertex.property
  simp only [inactive, OrientedState.sourceSelected, OrientedState.targetSelected, selectedActive,
    Bool.false_and, Bool.false_or, Bool.false_eq_true] at selected

theorem selectedComponentInterior_card (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    (Fintype.card (SelectedComponentInterior rule marks depth address parent) : ℝ) =
      markedOrientedVertexMass rule marks depth address parent := by
  classical
  simp only [SelectedComponentInterior, Fintype.card_subtype, markedOrientedVertexMass,
    internalStateMass, internalSelectedMass, Nat.cast_sum]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem generationCellInterior_joint_injective (rule : Rule) (depth : ℕ) :
    Function.Injective (fun pair : Fin rule.edges × (rule.generation depth).network.InteriorVertex =>
      rule.generationCellInterior depth pair.1 pair.2) := by
  intro first last equality
  have addresses := congrArg (rule.generationInteriorAddressEquiv (depth + 1)) equality
  simp only [rule.generationInteriorAddressEquiv_cell] at addresses
  have pairEquality := Sum.inr.inj addresses
  have edgeEquality : first.1 = last.1 := congrArg (fun pair : Fin rule.edges × rule.BirthAddress depth => pair.1) pairEquality
  have addressEquality := congrArg (fun pair : Fin rule.edges × rule.BirthAddress depth => pair.2) pairEquality
  exact Prod.ext edgeEquality ((rule.generationInteriorAddressEquiv depth).injective addressEquality)

def selectedComponentChildEmbedding (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    (Σ choice : Fin rule.edges × Bool, SelectedComponentInterior rule marks depth (address ++ [choice.1])
      (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) choice.1) choice.2)) ↪
      SelectedComponentInterior rule marks (depth + 1) address parent where
  toFun pair := ⟨rule.generationCellInterior depth pair.1.1 pair.2.val,
    embedded_split_component_selected rule marks crossing depth address parent pair.1.1 pair.1.2
      (selectedComponentInterior_live rule marks depth _ _ pair.2) pair.2.val.val pair.2.property⟩
  inj' := by
    rintro ⟨⟨firstEdge, firstSide⟩, firstVertex⟩ ⟨⟨lastEdge, lastSide⟩, lastVertex⟩ equality
    have interiors := congrArg (fun vertex => vertex.val) equality
    have pairEquality := generationCellInterior_joint_injective rule depth
      (a₁ := (firstEdge, firstVertex.val)) (a₂ := (lastEdge, lastVertex.val)) interiors
    have edgeEquality : firstEdge = lastEdge := congrArg Prod.fst pairEquality
    subst lastEdge
    have vertexEquality : firstVertex.val = lastVertex.val := congrArg Prod.snd pairEquality
    have firstLive := selectedComponentInterior_live rule marks depth _ _ firstVertex
    have lastLive := selectedComponentInterior_live rule marks depth _ _ lastVertex
    have firstBit := live_component_child_crossing_bit rule.network (marks (address, parent.massOpened))
      parent.sourceSelected parent.targetSelected firstEdge firstSide firstLive
    have lastBit := live_component_child_crossing_bit rule.network (marks (address, parent.massOpened))
      parent.sourceSelected parent.targetSelected firstEdge lastSide lastLive
    have firstSelected := firstVertex.property
    have lastSelected := lastVertex.property
    simp only [firstBit] at firstSelected
    simp only [lastBit, ← vertexEquality] at lastSelected
    have sideEquality : firstSide = lastSide := componentChildState_selected_unique
      (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth (address ++ [firstEdge]) (marks (address, parent.massOpened) firstEdge))
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) firstEdge)
      (by rw [markedGenerationConfiguration_crosses rule marks crossing, ← firstBit,
        live_split_child_massOpened _ _ firstLive]) firstSide lastSide firstVertex.val.val firstSelected lastSelected
    subst lastSide
    have selectedEquality : firstVertex = lastVertex := Subtype.ext vertexEquality
    subst lastVertex
    rfl

end
end IGSIII.Geometry