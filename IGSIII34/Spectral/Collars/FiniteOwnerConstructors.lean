import IGSIII34.Spectral.Collars.FiniteOwnershipLabels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

def selectedInteriorTransport
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine : ℕ) (firstAddress lastAddress : List (Fin rule.edges)) (firstState lastState : OrientedState)
    (addressEquality : firstAddress = lastAddress) (stateEquality : firstState = lastState)
    (vertex : SelectedComponentInterior rule marks fine firstAddress firstState) :
    SelectedComponentInterior rule marks fine lastAddress lastState := by
  cases addressEquality
  cases stateEquality
  exact vertex

theorem selectedInteriorTransport_vertex
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine : ℕ) (firstAddress lastAddress : List (Fin rule.edges)) (firstState lastState : OrientedState)
    (addressEquality : firstAddress = lastAddress) (stateEquality : firstState = lastState)
    (vertex : SelectedComponentInterior rule marks fine firstAddress firstState) :
    (selectedInteriorTransport rule marks fine firstAddress lastAddress firstState lastState
      addressEquality stateEquality vertex).val.val = vertex.val.val := by
  cases addressEquality
  cases stateEquality
  rfl

def rootComponentWordOwner
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (word : Fin age → (Fin rule.edges × Bool))
    (vertex : SelectedComponentInterior rule marks fine (componentEdgeAddress (List.ofFn word))
      (retainedComponentState rule marks (List.ofFn word))) :
    ComponentWordInterior rule marks fine age [] .connected :=
  ⟨word, vertex⟩

theorem rootComponentWordOwner_label
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (word : Fin age → (Fin rule.edges × Bool))
    (vertex : SelectedComponentInterior rule marks fine (componentEdgeAddress (List.ofFn word))
      (retainedComponentState rule marks (List.ofFn word))) :
    (rootComponentWordOwner rule marks fine age word vertex).1 = word := rfl

theorem rootComponentWordOwner_vertex
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (word : Fin age → (Fin rule.edges × Bool))
    (vertex : SelectedComponentInterior rule marks fine (componentEdgeAddress (List.ofFn word))
      (retainedComponentState rule marks (List.ofFn word))) :
    (rootComponentWordOwner rule marks fine age word vertex).2.val.val = vertex.val.val := rfl

end
end IGSIII34.Spectral
