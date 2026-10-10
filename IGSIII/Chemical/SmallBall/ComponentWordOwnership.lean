import IGSIII.Chemical.SmallBall.ComponentVertexOwnership
import IGSIII.Chemical.SmallBall.SigmaSubtypeCoordinates

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open scoped BigOperators

def ComponentWordInterior (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :=
  Σ word : Fin age → (Fin rule.edges × Bool), SelectedComponentInterior rule marks fine
    (ancestor ++ componentEdgeAddress (List.ofFn word))
    (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word))

instance componentWordInterior_fintype (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :
    Fintype (ComponentWordInterior rule marks fine age ancestor parent) := by
  unfold ComponentWordInterior
  infer_instance

theorem sigmaSubtype_point_ext {Index Point : Type*} {predicate : Index → Point → Prop}
    (first last : Σ index, {point : Point // predicate index point})
    (indexEquality : first.1 = last.1) (pointEquality : first.2.val = last.2.val) : first = last := by
  rcases first with ⟨firstIndex, firstPoint⟩
  rcases last with ⟨lastIndex, lastPoint⟩
  dsimp only at indexEquality pointEquality
  cases indexEquality
  exact congrArg (Sigma.mk firstIndex) (Subtype.ext pointEquality)
theorem componentWordInterior_point_ext (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (first last : ComponentWordInterior rule marks fine age ancestor parent)
    (indexEquality : first.1 = last.1) (pointEquality : first.2.val = last.2.val) : first = last := by
  exact sigmaSubtype_point_ext
    (predicate := fun (word : Fin age → (Fin rule.edges × Bool)) (point : (rule.generation fine).network.InteriorVertex) => (rule.generation fine).network.selectedActive
      (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).sourceSelected
      (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).targetSelected
      (markedGenerationConfiguration rule marks fine (ancestor ++ componentEdgeAddress (List.ofFn word))
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).massOpened) point.val = true)
    first last indexEquality pointEquality
def componentWordInteriorConsEquiv (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :
    ComponentWordInterior rule marks fine (age + 1) ancestor parent ≃
      Σ choice : Fin rule.edges × Bool, ComponentWordInterior rule marks fine age (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) := by
  refine consSubtypeEquiv age
    (fun word (point : (rule.generation fine).network.InteriorVertex) =>
      (rule.generation fine).network.selectedActive
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).sourceSelected
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).targetSelected
        (markedGenerationConfiguration rule marks fine (ancestor ++ componentEdgeAddress (List.ofFn word))
          (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).massOpened) point.val = true)
    (fun choice word (point : (rule.generation fine).network.InteriorVertex) =>
      (rule.generation fine).network.selectedActive
        (retainedComponentStateFrom rule marks (ancestor ++ [choice.1])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) choice.1) choice.2) (List.ofFn word)).sourceSelected
        (retainedComponentStateFrom rule marks (ancestor ++ [choice.1])
          (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (ancestor, parent.massOpened)) choice.1) choice.2) (List.ofFn word)).targetSelected
        (markedGenerationConfiguration rule marks fine
          ((ancestor ++ [choice.1]) ++ componentEdgeAddress (List.ofFn word))
          (retainedComponentStateFrom rule marks (ancestor ++ [choice.1])
            (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
              (marks (ancestor, parent.massOpened)) choice.1) choice.2) (List.ofFn word)).massOpened) point.val = true) ?_
  intro word point
  simp only [List.ofFn_succ, componentEdgeAddress, List.map_cons, retainedComponentStateFrom,
    List.append_assoc, List.singleton_append]
def componentWordInteriorHeadTail (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :
    ComponentWordInterior rule marks fine (age + 1) ancestor parent ↪
      Σ choice : Fin rule.edges × Bool, ComponentWordInterior rule marks fine age (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) :=
  (componentWordInteriorConsEquiv rule marks fine age ancestor parent).toEmbedding
def componentWordInteriorEmbeddingStep (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (child : ∀ choice : Fin rule.edges × Bool,
      ComponentWordInterior rule marks fine age (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) ↪
      SelectedComponentInterior rule marks (fine + age) (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2)) :
    ComponentWordInterior rule marks fine (age + 1) ancestor parent ↪
      SelectedComponentInterior rule marks (fine + (age + 1)) ancestor parent := by
  have combined :
      (Σ choice : Fin rule.edges × Bool, ComponentWordInterior rule marks fine age (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2)) ↪
      Σ choice : Fin rule.edges × Bool, SelectedComponentInterior rule marks (fine + age) (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl (Fin rule.edges × Bool)) child
  exact (componentWordInteriorHeadTail rule marks fine age ancestor parent).trans
      (combined.trans (selectedComponentChildEmbedding rule marks crossing (fine + age) ancestor parent))

def selectedComponentWordEmbedding (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine : ℕ) : (age : ℕ) → (ancestor : List (Fin rule.edges)) → (parent : OrientedState) →
      ComponentWordInterior rule marks fine age ancestor parent ↪
        SelectedComponentInterior rule marks (fine + age) ancestor parent
  | 0, ancestor, parent => {
      toFun := fun pair => ⟨pair.2.val, by
        simpa only [List.ofFn_zero, componentEdgeAddress, List.map_nil, List.append_nil,
          retainedComponentStateFrom, Nat.add_zero] using pair.2.property⟩
      inj' := by
        rintro ⟨word, vertex⟩ ⟨other, otherVertex⟩ equality
        have wordEquality : word = other := Subsingleton.elim _ _
        exact componentWordInterior_point_ext rule marks fine _ ancestor parent ⟨word, vertex⟩ ⟨other, otherVertex⟩ wordEquality
          (congrArg (fun vertex => vertex.val) equality) }
  | age + 1, ancestor, parent => componentWordInteriorEmbeddingStep rule marks crossing fine age ancestor parent
      (fun choice => selectedComponentWordEmbedding rule marks crossing fine age (ancestor ++ [choice.1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) choice.1) choice.2))
termination_by age => age

end
end IGSIII.Geometry