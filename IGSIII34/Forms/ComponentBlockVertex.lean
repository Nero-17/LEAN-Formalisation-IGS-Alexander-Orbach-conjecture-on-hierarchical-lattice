import IGSIII34.Diffusion.ActualComponentBirthEmbeddingIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Diffusion

theorem generationComponentWordEmbedding_block_vertex (rule : Rule) (coarse fine : ℕ)
    (word : Fin (coarse + 1) → Fin rule.edges) (sourceSide : Bool)
    (configuration : Configuration (rule.generation fine).edges)
    (vertex : Fin (rule.generation fine).vertices)
    (retained : ((rule.generation fine).network.openGraph configuration).Reachable
      (plantedVertex (rule.generation fine).network sourceSide) vertex) :
    Fin.cast (congrArg (fun depth => (rule.generation depth).vertices)
      (by omega : fine + (coarse + 1) = coarse + fine + 1))
      ((generationComponentWordEmbedding rule fine (coarse + 1) word).vertex vertex) =
    (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse word)).vertex vertex := by
  have identity := generationComponentWordEmbedding_address rule fine (coarse + 1) word
  have transferred := eq_of_heq (dependentMap_heq
    (fun length (embedding : (rule.generation fine).network.NetworkEmbedding
      (rule.generation (fine + length)).network) => (embedding.vertex vertex).val)
    (show coarse + 1 = (List.ofFn word).length by simp only [List.length_ofFn]) identity)
  have block := generationAddressEmbedding_block_vertex rule coarse fine word sourceSide configuration vertex retained
  rw [generationEmbeddingAtIndex_vertex] at block
  apply Fin.ext
  simp only [Fin.val_cast]
  exact transferred.trans (by simpa only [Fin.val_cast] using congrArg Fin.val block)

end
end IGSIII34.Forms
