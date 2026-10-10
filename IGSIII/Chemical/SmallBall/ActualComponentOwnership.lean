import IGSIII.Chemical.SmallBall.ComponentWordOwnership
import IGSIII.Chemical.SmallBall.FiniteComponentOwnership

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Classical
open scoped BigOperators

def actualComponentInteriorOwnership (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    SelectedComponentInterior rule marks (fine + age) [] .connected → Fin age → (Fin rule.edges × Bool) :=
  finiteComponentOwnership (selectedComponentWordEmbedding rule marks crossing fine age [] .connected) fallback

def actualComponentInteriorFrontier (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) : Finset (SelectedComponentInterior rule marks (fine + age) [] .connected) :=
  finiteComponentFrontier (selectedComponentWordEmbedding rule marks crossing fine age [] .connected)

theorem actualComponentInteriorFrontier_card (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) :
    ((actualComponentInteriorFrontier rule marks crossing fine age).card : ℝ) =
      componentFrontierVertexMass rule marks age [] := by
  have partition := finiteComponentFrontier_card_partition
    (selectedComponentWordEmbedding rule marks crossing fine age [] .connected)
  have realPartition := congrArg (fun count : ℕ => (count : ℝ)) partition
  simp only [Nat.cast_add, Nat.cast_sum, selectedComponentInterior_card] at realPartition
  have actualPartition := actual_component_finite_partition rule marks crossing fine age []
  simp only [markedComponentVertexMass, retainedComponentState, retainedComponentStateFrom,
    componentEdgeAddress, List.map_nil, List.nil_append] at actualPartition
  simp only [componentEdgeAddress, List.nil_append] at realPartition
  change ((finiteComponentFrontier (selectedComponentWordEmbedding rule marks crossing fine age [] .connected)).card : ℝ) = _
  linarith

theorem actualComponentInteriorOwnership_fiber_card (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool)) :
    ((Finset.univ.filter (fun point => actualComponentInteriorOwnership rule marks crossing fine age fallback point = word)).card : ℝ) =
      markedComponentVertexMass rule marks fine (List.ofFn word) +
        if word = fallback then componentFrontierVertexMass rule marks age [] else 0 := by
  have equality := finiteComponentOwnership_fiber_card
    (selectedComponentWordEmbedding rule marks crossing fine age [] .connected) fallback word
  have realEquality := congrArg (fun count : ℕ => (count : ℝ)) equality
  simpa only [actualComponentInteriorOwnership, Nat.cast_add, Nat.cast_ite, Nat.cast_zero,
    selectedComponentInterior_card, markedComponentVertexMass, retainedComponentState,
    List.nil_append, ← actualComponentInteriorFrontier_card rule marks crossing fine age,
    actualComponentInteriorFrontier] using realEquality

theorem actualComponentInteriorOwnership_nonfrontier (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool))
    (point : SelectedComponentInterior rule marks (fine + age) [] .connected)
    (nonfrontier : point ∉ actualComponentInteriorFrontier rule marks crossing fine age) :
    ∃ child : SelectedComponentInterior rule marks fine
        (componentEdgeAddress (List.ofFn (actualComponentInteriorOwnership rule marks crossing fine age fallback point)))
        (retainedComponentState rule marks (List.ofFn (actualComponentInteriorOwnership rule marks crossing fine age fallback point))),
      selectedComponentWordEmbedding rule marks crossing fine age [] .connected
        ⟨actualComponentInteriorOwnership rule marks crossing fine age fallback point, child⟩ = point := by
  exact finiteComponentOwnership_inside (selectedComponentWordEmbedding rule marks crossing fine age [] .connected) fallback point nonfrontier
theorem actualComponentInteriorOwnership_empirical_weight (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool))
    (massPositive : 0 < markedComponentVertexMass rule marks (fine + age) []) :
    ((Finset.univ.filter (fun point => actualComponentInteriorOwnership rule marks crossing fine age fallback point = word)).card : ℝ) /
      Fintype.card (SelectedComponentInterior rule marks (fine + age) [] .connected) =
      componentEmpiricalWordWeight rule marks fine age fallback word := by
  rw [componentEmpiricalWordWeight, if_pos massPositive, actualComponentInteriorOwnership_fiber_card,
    selectedComponentInterior_card]
  rfl

end
end IGSIII.Geometry