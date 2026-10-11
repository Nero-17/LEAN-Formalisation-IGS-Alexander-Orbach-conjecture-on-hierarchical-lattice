import IGSIII34.Spectral.Collars.FiniteOwnershipVertexInjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

theorem selected_component_word_labels_eq_of_vertex_eq
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (first last : ComponentWordInterior rule marks fine age ancestor parent)
    (equality : (selectedComponentWordEmbedding rule marks crossing fine age ancestor parent first).val.val =
      (selectedComponentWordEmbedding rule marks crossing fine age ancestor parent last).val.val) :
    first.1 = last.1 :=
  congrArg (fun owner : ComponentWordInterior rule marks fine age ancestor parent => owner.1)
    (selected_component_word_ownership_vertex_injective rule marks crossing fine age ancestor parent equality)

end
end IGSIII34.Spectral
