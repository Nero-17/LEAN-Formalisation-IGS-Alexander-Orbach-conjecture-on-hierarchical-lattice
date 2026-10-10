import Universality.Graph.NetworkEquivalence

namespace Universality.FiniteNetwork
noncomputable section

/-- An embedding of indexed networks. A child cell need not send its terminals
to the terminals of the containing network. -/
structure NetworkEmbedding {vR eR vS eS : ℕ}
    (R : FiniteNetwork vR eR) (S : FiniteNetwork vS eS) where
  vertex : Fin vR ↪ Fin vS
  edge : Fin eR ↪ Fin eS
  endpoint : ∀ e, S.endpoint (edge e) =
    (vertex (R.endpoint e).1, vertex (R.endpoint e).2)

namespace NetworkEmbedding
variable {vR eR vS eS vT eT : ℕ}
variable {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
variable {T : FiniteNetwork vT eT}

def refl (R : FiniteNetwork vR eR) : R.NetworkEmbedding R where
  vertex := Function.Embedding.refl _
  edge := Function.Embedding.refl _
  endpoint _ := rfl

def trans (first : R.NetworkEmbedding S) (second : S.NetworkEmbedding T) :
    R.NetworkEmbedding T where
  vertex := first.vertex.trans second.vertex
  edge := first.edge.trans second.edge
  endpoint e := by
    change T.endpoint (second.edge (first.edge e)) = _
    rw [second.endpoint, first.endpoint]
    rfl

def ofEquivalence (equivalence : R.NetworkEquivalence S) : R.NetworkEmbedding S where
  vertex := equivalence.vertex.toEmbedding
  edge := equivalence.edge.toEmbedding
  endpoint := equivalence.endpoint

/-- Restrict any configuration on the larger network to its embedded edges. -/
def restrict (embedding : R.NetworkEmbedding S) (configuration : Configuration eS) :
    Configuration eR := fun edge => configuration (embedding.edge edge)

def openGraphHom (embedding : R.NetworkEmbedding S) (configuration : Configuration eS) :
    R.openGraph (embedding.restrict configuration) →g S.openGraph configuration where
  toFun := embedding.vertex
  map_rel' := by
    intro x y adjacency
    rcases adjacency with ⟨hne, edge, hopen, hpair | hpair⟩
    · refine ⟨fun heq => hne (embedding.vertex.injective heq), embedding.edge edge,
        hopen, Or.inl ?_⟩
      rw [embedding.endpoint, hpair]
    · refine ⟨fun heq => hne (embedding.vertex.injective heq), embedding.edge edge,
        hopen, Or.inr ?_⟩
      rw [embedding.endpoint, hpair]

end NetworkEmbedding

/-- The actual indexed child network embedded into an edge substitution. -/
def cellNetworkEmbedding {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (edge : Fin outerEdges) : S.NetworkEmbedding (R.substitute S) where
  vertex := ⟨fun x => Fintype.equivFin _ (R.cellVertex S edge x),
    (Fintype.equivFin _).injective.comp (R.cellVertex_injective S edge)⟩
  edge := ⟨fun child => finProdFinEquiv (edge, child), by
    intro child other heq
    exact congrArg Prod.snd (finProdFinEquiv.injective heq)⟩
  endpoint := R.substitute_endpoint S edge

end
end Universality.FiniteNetwork

