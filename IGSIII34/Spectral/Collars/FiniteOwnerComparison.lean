import IGSIII34.Spectral.Collars.FiniteOwnerConstructors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry


/-- Compare actual finite owners while keeping the generation parameter
abstract. This prevents reduction of the recursive successor embedding. -/
theorem component_words_eq_of_common_finite_interior
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (first last : Fin age → (Fin rule.edges × Bool))
    (sameEdges : (fun index => (first index).1) = fun index => (last index).1)
    (sameState : retainedComponentState rule marks (List.ofFn first) =
      retainedComponentState rule marks (List.ofFn last))
    (vertex : SelectedComponentInterior rule marks fine
      (componentEdgeAddress (List.ofFn first)) (retainedComponentState rule marks (List.ofFn first))) :
    first = last := by
  have sameAddress : componentEdgeAddress (List.ofFn first) = componentEdgeAddress (List.ofFn last) := by
    simpa only [componentEdgeAddress, List.map_ofFn, Function.comp_def] using congrArg List.ofFn sameEdges
  let otherVertex := selectedInteriorTransport rule marks fine
    (componentEdgeAddress (List.ofFn first)) (componentEdgeAddress (List.ofFn last))
    (retainedComponentState rule marks (List.ofFn first)) (retainedComponentState rule marks (List.ofFn last))
    sameAddress sameState vertex
  let firstOwner := rootComponentWordOwner rule marks fine age first vertex
  let lastOwner := rootComponentWordOwner rule marks fine age last otherVertex
  have sameEmbedded : (selectedComponentWordEmbedding rule marks crossing fine age [] .connected firstOwner).val.val =
      (selectedComponentWordEmbedding rule marks crossing fine age [] .connected lastOwner).val.val := by
    dsimp only [firstOwner, lastOwner]
    rw [selectedComponentWordEmbedding_vertex, selectedComponentWordEmbedding_vertex]
    simp only [rootComponentWordOwner_label, rootComponentWordOwner_vertex]
    dsimp only [otherVertex]
    rw [selectedInteriorTransport_vertex, sameEdges]
  have labels := selected_component_word_labels_eq_of_vertex_eq rule marks crossing fine age [] .connected
    firstOwner lastOwner sameEmbedded
  dsimp only [firstOwner, lastOwner] at labels
  simpa only [rootComponentWordOwner_label] using labels

end
end IGSIII34.Spectral
