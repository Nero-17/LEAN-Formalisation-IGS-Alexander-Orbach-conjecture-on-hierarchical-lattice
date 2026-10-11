import IGSIII34.Diffusion.ActualElectricalComponentFiniteInclusion
import IGSIII.Geometry.ComponentWordMetric
import IGSIII.Geometry.ActualBlockCellEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

/-- Reindexing the containing generation changes no actual vertex label. -/
def generationEmbeddingAtIndex (rule : Rule) (fine first second : ℕ) (equal : first = second)
    (embedding : (rule.generation fine).network.NetworkEmbedding (rule.generation first).network) :
    (rule.generation fine).network.NetworkEmbedding (rule.generation second).network :=
  equal ▸ embedding

theorem generationEmbeddingAtIndex_vertex (rule : Rule) (fine first second : ℕ) (equal : first = second)
    (embedding : (rule.generation fine).network.NetworkEmbedding (rule.generation first).network)
    (vertex : Fin (rule.generation fine).vertices) :
    (generationEmbeddingAtIndex rule fine first second equal embedding).vertex vertex =
      Fin.cast (congrArg (fun depth => (rule.generation depth).vertices) equal) (embedding.vertex vertex) := by
  cases equal
  rfl

theorem generationEmbeddingAtIndex_edge (rule : Rule) (fine first second : ℕ) (equal : first = second)
    (embedding : (rule.generation fine).network.NetworkEmbedding (rule.generation first).network)
    (edge : Fin (rule.generation fine).edges) :
    (generationEmbeddingAtIndex rule fine first second equal embedding).edge edge =
      Fin.cast (congrArg (fun depth => (rule.generation depth).edges) equal) (embedding.edge edge) := by
  cases equal
  rfl

theorem generationEdgeAddress_cast (rule : Rule) (first second : ℕ) (equal : first = second)
    (edge : Fin (rule.generation first).edges) :
    generationEdgeAddress rule second (Fin.cast (congrArg (fun depth => (rule.generation depth).edges) equal) edge) =
      generationEdgeAddress rule first edge := by
  cases equal
  rfl

theorem persistentVertexEmbedding_val_index (rule : Rule) (coarse first last : ℕ)
    (equal : first = last) (firstBound : coarse ≤ first) (lastBound : coarse ≤ last)
    (vertex : Fin (rule.generation coarse).vertices) :
    (persistentVertexEmbedding rule coarse first firstBound vertex).val =
      (persistentVertexEmbedding rule coarse last lastBound vertex).val := by
  cases equal
  rfl

/-- Equality on indexed edges and the planted anchor fixes every retained
vertex, including an isolated planted component. -/
theorem networkEmbedding_vertex_eq_on_reachable
    {firstVertices firstEdges lastVertices lastEdges : ℕ}
    (first : Universality.FiniteNetwork firstVertices firstEdges)
    (last : Universality.FiniteNetwork lastVertices lastEdges)
    (left right : first.NetworkEmbedding last) (configuration : Configuration firstEdges)
    (edges : ∀ edge, left.edge edge = right.edge edge)
    (anchor vertex : Fin firstVertices) (atAnchor : left.vertex anchor = right.vertex anchor)
    (reachable : (first.openGraph configuration).Reachable anchor vertex) :
    left.vertex vertex = right.vertex vertex := by
  by_cases same : anchor = vertex
  · simpa only [same] using atAnchor
  · obtain ⟨neighbor, adjacent⟩ := reachable.nonempty_neighborSet_right same
    rcases adjacent with ⟨_, edge, _, endpoints | endpoints⟩
    · have identity := congrArg Prod.fst ((left.endpoint edge).symm.trans
        ((congrArg last.endpoint (edges edge)).trans (right.endpoint edge)))
      simpa only [endpoints] using identity
    · have identity := congrArg Prod.snd ((left.endpoint edge).symm.trans
        ((congrArg last.endpoint (edges edge)).trans (right.endpoint edge)))
      simpa only [endpoints] using identity

theorem generationAddressEmbedding_block_edge (rule : Rule) (coarse fine : ℕ)
    (word : Fin (coarse + 1) → Fin rule.edges) (edge : Fin (rule.generation fine).edges) :
    (generationEmbeddingAtIndex rule fine (fine + (List.ofFn word).length) (coarse + fine + 1)
      (by simp only [List.length_ofFn]; omega) (generationAddressEmbedding rule (List.ofFn word) fine)).edge edge =
      (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse word)).edge edge := by
  apply generationEdgeAddress_injective rule (coarse + fine + 1)
  rw [generationEmbeddingAtIndex_edge, generationEdgeAddress_cast,
    generationEdgeAddress_addressEmbedding]
  change _ = generationEdgeAddress rule (coarse + fine + 1)
    ((rule.generationBlockDecomposition coarse fine).edge.symm
      (finProdFinEquiv (generationWordEdge rule coarse word, edge)))
  rw [generationEdgeAddress_block, generationWordEdge_address]
  simp only [List.length_ofFn]
  omega

/-- The top-down original address and the coarse block embedding agree on
every original retained vertex, with the exact index transport displayed. -/
theorem generationAddressEmbedding_block_vertex (rule : Rule) (coarse fine : ℕ)
    (word : Fin (coarse + 1) → Fin rule.edges) (sourceSide : Bool)
    (configuration : Configuration (rule.generation fine).edges)
    (vertex : Fin (rule.generation fine).vertices)
    (retained : ((rule.generation fine).network.openGraph configuration).Reachable
      (plantedVertex (rule.generation fine).network sourceSide) vertex) :
    (generationEmbeddingAtIndex rule fine (fine + (List.ofFn word).length) (coarse + fine + 1)
      (by simp only [List.length_ofFn]; omega) (generationAddressEmbedding rule (List.ofFn word) fine)).vertex vertex =
      (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse word)).vertex vertex := by
  apply networkEmbedding_vertex_eq_on_reachable (rule.generation fine).network
    (rule.generation (coarse + fine + 1)).network _ _ configuration
    (generationAddressEmbedding_block_edge rule coarse fine word)
    (plantedVertex (rule.generation fine).network sourceSide) vertex ?_ retained
  rw [generationEmbeddingAtIndex_vertex]
  apply Fin.ext
  simp only [Fin.val_cast]
  have identity := generationComponentWordEmbedding_address rule fine (coarse + 1) word
  have transferred := eq_of_heq (dependentMap_heq
    (fun length (embedding : (rule.generation fine).network.NetworkEmbedding (rule.generation (fine + length)).network) =>
      (embedding.vertex (plantedVertex (rule.generation fine).network sourceSide)).val)
    (show coarse + 1 = (List.ofFn word).length by simp only [List.length_ofFn]) identity)
  rw [← transferred, generationComponentWordEmbedding_planted]
  cases sourceSide with
  | false =>
      rw [show plantedVertex (rule.generation fine).network false = (rule.generation fine).network.target by rfl,
        generationBlockCellEmbedding_target, blockOldVertexEmbedding_eq_persistent]
      simp only [Bool.false_eq_true, if_false]
      exact persistentVertexEmbedding_val_index rule coarse (fine + coarse + 1) (coarse + fine + 1) (by omega) _ _ _
  | true =>
      rw [show plantedVertex (rule.generation fine).network true = (rule.generation fine).network.source by rfl,
        generationBlockCellEmbedding_source, blockOldVertexEmbedding_eq_persistent]
      simp only [if_true]
      exact persistentVertexEmbedding_val_index rule coarse (fine + coarse + 1) (coarse + fine + 1) (by omega) _ _ _

end
end IGSIII34.Diffusion
