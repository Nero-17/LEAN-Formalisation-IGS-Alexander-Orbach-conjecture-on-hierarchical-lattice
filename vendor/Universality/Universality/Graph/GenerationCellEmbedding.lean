import Universality.Graph.NetworkEmbedding
import Universality.Graph.GenerationReassociation

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- A generation is an actual child cell of the next generation. The selected
outer edge supplies the next symbol of an ancestral edge address. -/
def generationCellEmbedding (rule : Rule) (depth : ℕ) (edge : Fin rule.edges) :
    (rule.generation depth).network.NetworkEmbedding (rule.generation (depth + 1)).network :=
  (rule.network.cellNetworkEmbedding (rule.generation depth).network edge).trans
    (NetworkEmbedding.ofEquivalence (rule.generationTopDecomposition depth).symm)

theorem generationCellEmbedding_endpoint (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) :
    (rule.generation (depth + 1)).network.endpoint
        ((rule.generationCellEmbedding depth edge).edge child) =
      ((rule.generationCellEmbedding depth edge).vertex
          ((rule.generation depth).network.endpoint child).1,
        (rule.generationCellEmbedding depth edge).vertex
          ((rule.generation depth).network.endpoint child).2) :=
  (rule.generationCellEmbedding depth edge).endpoint child

end
end Universality.Rule

