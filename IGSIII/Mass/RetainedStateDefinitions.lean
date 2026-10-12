import Universality.Percolation.OrientedStates

set_option autoImplicit false

namespace IGSIII.Mass

open Universality Universality.FiniteNetwork

/-- The actual inherited-state classifier has exactly the four live states
used in the manuscript, together with the inactive state. -/
theorem actual_retained_state_classifier :
    orientedStateOf true true true = OrientedState.connected ∧
    orientedStateOf true true false = OrientedState.both ∧
    orientedStateOf true false true = OrientedState.sourceOnly ∧
    orientedStateOf true false false = OrientedState.sourceOnly ∧
    orientedStateOf false true true = OrientedState.targetOnly ∧
    orientedStateOf false true false = OrientedState.targetOnly ∧
    orientedStateOf false false true = OrientedState.inactive ∧
    orientedStateOf false false false = OrientedState.inactive :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Selection retains the union of precisely the selected planted components. -/
theorem actual_retained_selection_definition {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (sourceSelected targetSelected : Bool)
    (configuration : Configuration edges) (vertex : Fin vertices) :
    network.selectedActive sourceSelected targetSelected configuration vertex =
      ((sourceSelected && (network.openGraph configuration).reachableDecide network.source vertex) ||
       (targetSelected && (network.openGraph configuration).reachableDecide network.target vertex)) :=
  rfl

/-- Every child inherits its endpoint selections from the same actual parent
configuration. No independent resampling of the two sides is introduced. -/
theorem actual_retained_child_state_definition {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (sourceSelected targetSelected : Bool)
    (configuration : Configuration edges) (edge : Fin edges) :
    network.orientedChildState sourceSelected targetSelected configuration edge =
      orientedStateOf
        (network.selectedActive sourceSelected targetSelected configuration (network.endpoint edge).1)
        (network.selectedActive sourceSelected targetSelected configuration (network.endpoint edge).2)
        (configuration edge) :=
  rfl

end IGSIII.Mass
