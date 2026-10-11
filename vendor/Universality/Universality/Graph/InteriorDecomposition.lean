import Universality.Graph.GenerationCellEmbedding
import Universality.Percolation.InternalVertexMass

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}

def NetworkEquivalence.mapInterior (equivalence : R.NetworkEquivalence S)
    (v : R.InteriorVertex) : S.InteriorVertex :=
  ⟨equivalence.vertex v.val, by
    constructor
    · rw [← equivalence.source]
      exact fun h => v.property.1 (equivalence.vertex.injective h)
    · rw [← equivalence.target]
      exact fun h => v.property.2 (equivalence.vertex.injective h)⟩

def NetworkEquivalence.interiorEquiv (equivalence : R.NetworkEquivalence S) :
    R.InteriorVertex ≃ S.InteriorVertex where
  toFun := equivalence.mapInterior
  invFun := equivalence.symm.mapInterior
  left_inv v := Subtype.ext (equivalence.vertex.symm_apply_apply v.val)
  right_inv v := Subtype.ext (equivalence.vertex.apply_symm_apply v.val)

end
end Universality.FiniteNetwork

