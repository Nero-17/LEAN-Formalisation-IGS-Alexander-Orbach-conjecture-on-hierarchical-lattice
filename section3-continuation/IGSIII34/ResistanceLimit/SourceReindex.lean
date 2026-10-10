import IGSIII34.ResistanceLimit.SourceEnergy
import IGSIII34.ResistanceLimit.PairReindex

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork

variable {Vertex Edge OtherVertex OtherEdge : Type*}
  [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
  [Fintype OtherVertex] [DecidableEq OtherVertex] [Fintype OtherEdge] [DecidableEq OtherEdge]

theorem sourceComponentEnergy_reindex
    (network : Resistance.FiniteNetwork Vertex Edge) (other : Resistance.FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ≃ OtherVertex) (edges : Edge ≃ OtherEdge)
    (endpoint : ∀ edge, other.endpoint (edges edge) =
      (vertices (network.endpoint edge).1, vertices (network.endpoint edge).2))
    (source : other.source = vertices network.source)
    (resistance : Edge → ℝ) (potential : OtherVertex → ℝ) :
    sourceComponentEnergy other (fun edge => resistance (edges.symm edge)) potential =
      sourceComponentEnergy network resistance (fun vertex => potential (vertices vertex)) := by
  have inverseEndpoint (edge : OtherEdge) : network.endpoint (edges.symm edge) =
      (vertices.symm (other.endpoint edge).1, vertices.symm (other.endpoint edge).2) := by
    have identity := endpoint (edges.symm edge)
    rw [Equiv.apply_symm_apply] at identity
    apply Prod.ext
    · exact (vertices.symm_apply_eq.mpr (congrArg Prod.fst identity)).symm
    · exact (vertices.symm_apply_eq.mpr (congrArg Prod.snd identity)).symm
  let forward := networkEmbeddingGraphHom network other vertices.toEmbedding edges.toEmbedding endpoint
  let backward := networkEmbeddingGraphHom other network vertices.symm.toEmbedding edges.symm.toEmbedding inverseEndpoint
  have forwardValues (vertex : Vertex) : forward vertex = vertices vertex := rfl
  have backwardValues (vertex : OtherVertex) : backward vertex = vertices.symm vertex := rfl
  have reachability (vertex : Vertex) : other.graph.Reachable other.source (vertices vertex) ↔
      network.graph.Reachable network.source vertex := by
    rw [source]
    constructor
    · intro reachable
      simpa only [backwardValues, Equiv.symm_apply_apply] using reachable.map backward
    · intro reachable
      simpa only [forwardValues] using reachable.map forward
  unfold sourceComponentEnergy finiteEnergy
  rw [← edges.sum_comp]
  simp only [Equiv.symm_apply_apply, endpoint, reachability]

end
end IGSIII34.ResistanceLimit
