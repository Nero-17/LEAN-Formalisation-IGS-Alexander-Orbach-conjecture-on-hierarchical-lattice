import IGSIII34.Diffusion.EdgeFinitePartition
import IGSIII.Geometry.ComponentWordMetric
import IGSIII.Geometry.FiniteUniformOwnership

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

def SelectedComponentEdge (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :=
  {edge : Fin (rule.generation depth).edges //
    (rule.generation depth).network.orientedChildState parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks depth address parent.massOpened) edge = .connected}

instance selectedComponentEdge_fintype (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    Fintype (SelectedComponentEdge rule marks depth address parent) := by
  classical
  unfold SelectedComponentEdge
  infer_instance

theorem selectedComponentEdge_live (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState)
    (edge : SelectedComponentEdge rule marks depth address parent) : parent ≠ .inactive := by
  intro inactive
  have connected := edge.property
  simp [inactive, orientedChildState, OrientedState.sourceSelected, OrientedState.targetSelected,
    selectedActive, orientedStateOf] at connected

theorem selectedComponentEdge_card (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    (Fintype.card (SelectedComponentEdge rule marks depth address parent) : ℝ) =
      markedOrientedEdgeMass rule marks depth address parent := by
  classical
  simp only [SelectedComponentEdge, Fintype.card_subtype, markedOrientedEdgeMass,
    orientedEdgeReward, orientedLiveCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

def selectedComponentChildEdgeEmbedding (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    (Σ choice : Fin rule.edges × Bool, SelectedComponentEdge rule marks depth (address ++ [choice.1])
      (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) choice.1) choice.2)) ↪
      SelectedComponentEdge rule marks (depth + 1) address parent where
  toFun pair := ⟨(rule.generationCellEmbedding depth pair.1.1).edge pair.2.val, by
    have live := selectedComponentEdge_live rule marks depth _ _ pair.2
    have selected := ((rule.generation depth).network.orientedChildState_connected_iff _ _ _ _).mp pair.2.property
    apply ((rule.generation (depth + 1)).network.orientedChildState_connected_iff _ _ _ _).mpr
    constructor
    · change markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened
        ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (pair.1.1, pair.2.val))) = true
      rw [markedGenerationConfiguration_top_apply]
      rw [← live_component_child_crossing_bit rule.network _ _ _ _ _ live]
      exact selected.1
    · rw [(rule.generationCellEmbedding depth pair.1.1).endpoint]
      exact embedded_split_component_selected rule marks crossing depth address parent pair.1.1 pair.1.2
        live _ selected.2⟩
  inj' := by
    rintro ⟨⟨firstEdge, firstSide⟩, firstChild⟩ ⟨⟨lastEdge, lastSide⟩, lastChild⟩ equality
    have raw := congrArg (fun edge : SelectedComponentEdge rule marks (depth + 1) address parent => edge.val) equality
    change (rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (firstEdge, firstChild.val)) =
      (rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (lastEdge, lastChild.val)) at raw
    have coordinates := congrArg (fun edge => finProdFinEquiv.symm ((rule.generationTopDecomposition depth).edge edge)) raw
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at coordinates
    have edgeEquality : firstEdge = lastEdge := congrArg Prod.fst coordinates
    subst lastEdge
    have childEquality : firstChild.val = lastChild.val := congrArg Prod.snd coordinates
    have firstLive := selectedComponentEdge_live rule marks depth _ _ firstChild
    have lastLive := selectedComponentEdge_live rule marks depth _ _ lastChild
    have firstBit := live_component_child_crossing_bit rule.network (marks (address, parent.massOpened))
      parent.sourceSelected parent.targetSelected firstEdge firstSide firstLive
    have lastBit := live_component_child_crossing_bit rule.network (marks (address, parent.massOpened))
      parent.sourceSelected parent.targetSelected firstEdge lastSide lastLive
    have firstSelected := ((rule.generation depth).network.orientedChildState_connected_iff _ _ _ _).mp firstChild.property
    have lastSelected := ((rule.generation depth).network.orientedChildState_connected_iff _ _ _ _).mp lastChild.property
    simp only [firstBit] at firstSelected
    simp only [lastBit, ← childEquality] at lastSelected
    have sideEquality : firstSide = lastSide := componentChildState_selected_unique
      (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth (address ++ [firstEdge]) (marks (address, parent.massOpened) firstEdge))
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) firstEdge)
      (by rw [markedGenerationConfiguration_crosses rule marks crossing, ← firstBit,
        live_split_child_massOpened _ _ firstLive]) firstSide lastSide
      ((rule.generation depth).network.endpoint firstChild.val).1 firstSelected.2 lastSelected.2
    subst lastSide
    have selectedEquality : firstChild = lastChild := Subtype.ext childEquality
    subst lastChild
    rfl

def ComponentWordEdge (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :=
  Σ word : Fin age → (Fin rule.edges × Bool), SelectedComponentEdge rule marks fine
    (ancestor ++ componentEdgeAddress (List.ofFn word))
    (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word))

instance componentWordEdge_fintype (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :
    Fintype (ComponentWordEdge rule marks fine age ancestor parent) := by
  unfold ComponentWordEdge
  infer_instance

def componentWordEdgeConsEquiv (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :
    ComponentWordEdge rule marks fine (age + 1) ancestor parent ≃
      Σ choice : Fin rule.edges × Bool, ComponentWordEdge rule marks fine age (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) := by
  refine consSubtypeEquiv age
    (fun word (edge : Fin (rule.generation fine).edges) =>
      (rule.generation fine).network.orientedChildState
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).sourceSelected
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).targetSelected
        (markedGenerationConfiguration rule marks fine (ancestor ++ componentEdgeAddress (List.ofFn word))
          (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).massOpened) edge = .connected)
    (fun choice word (edge : Fin (rule.generation fine).edges) =>
      (rule.generation fine).network.orientedChildState
        (retainedComponentStateFrom rule marks (ancestor ++ [choice.1])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) choice.1) choice.2) (List.ofFn word)).sourceSelected
        (retainedComponentStateFrom rule marks (ancestor ++ [choice.1])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) choice.1) choice.2) (List.ofFn word)).targetSelected
        (markedGenerationConfiguration rule marks fine ((ancestor ++ [choice.1]) ++ componentEdgeAddress (List.ofFn word))
          (retainedComponentStateFrom rule marks (ancestor ++ [choice.1])
            (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
              (marks (ancestor, parent.massOpened)) choice.1) choice.2) (List.ofFn word)).massOpened) edge = .connected) ?_
  intro word edge
  simp only [List.ofFn_succ, componentEdgeAddress, List.map_cons, retainedComponentStateFrom,
    List.append_assoc, List.singleton_append]

def selectedComponentWordEdgeEmbedding (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine : ℕ) : (age : ℕ) → (ancestor : List (Fin rule.edges)) → (parent : OrientedState) →
      ComponentWordEdge rule marks fine age ancestor parent ↪
        SelectedComponentEdge rule marks (fine + age) ancestor parent
  | 0, ancestor, parent => {
      toFun := fun pair => ⟨pair.2.val, by
        simpa only [List.ofFn_zero, componentEdgeAddress, List.map_nil, List.append_nil,
          retainedComponentStateFrom, Nat.add_zero] using pair.2.property⟩
      inj' := by
        rintro ⟨word, edge⟩ ⟨other, otherEdge⟩ equality
        have wordEquality : word = other := Subsingleton.elim _ _
        subst other
        have raw := congrArg (fun point : SelectedComponentEdge rule marks fine ancestor parent => point.val) equality
        change edge.val = otherEdge.val at raw
        have edgeEquality : edge = otherEdge := Subtype.ext raw
        subst otherEdge
        rfl }
  | age + 1, ancestor, parent =>
      (componentWordEdgeConsEquiv rule marks fine age ancestor parent).toEmbedding.trans
        ((Function.Embedding.sigmaMap (Function.Embedding.refl (Fin rule.edges × Bool))
          (fun choice => selectedComponentWordEdgeEmbedding rule marks crossing fine age (ancestor ++ [choice.1])
            (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
              (marks (ancestor, parent.massOpened)) choice.1) choice.2))).trans
          (selectedComponentChildEdgeEmbedding rule marks crossing (fine + age) ancestor parent))
termination_by age => age

end
end IGSIII34.Diffusion
