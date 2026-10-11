import IGSIII34.Spectral.Collars.FiniteOwnershipInjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

theorem selected_component_word_ownership_vertex_injective
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :
    Function.Injective (fun owner : ComponentWordInterior rule marks fine age ancestor parent =>
      (selectedComponentWordEmbedding rule marks crossing fine age ancestor parent owner).val.val) := by
  intro first last equality
  apply selected_component_word_ownership_injective rule marks crossing fine age ancestor parent
  exact Subtype.ext (Subtype.ext equality)

end
end IGSIII34.Spectral
