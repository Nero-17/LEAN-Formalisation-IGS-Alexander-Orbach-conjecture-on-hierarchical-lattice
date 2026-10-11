import IGSIII.Chemical.SmallBall.ComponentOwnershipEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

/-- Keep the recursive finite ownership injection behind its proved
theorem interface when applying it to a successor generation. -/
theorem selected_component_word_ownership_injective
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState) :
    Function.Injective (selectedComponentWordEmbedding rule marks crossing fine age ancestor parent) :=
  (selectedComponentWordEmbedding rule marks crossing fine age ancestor parent).injective


end
end IGSIII34.Spectral
