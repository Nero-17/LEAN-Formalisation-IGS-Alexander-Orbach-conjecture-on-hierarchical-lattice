import IGSIII34.ResistanceLimit.ElectricalRadius
import IGSIII34.Resistance.Reindex

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork

variable {Vertex Edge OtherVertex OtherEdge : Type*}
  [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
  [Fintype OtherVertex] [DecidableEq OtherVertex] [Fintype OtherEdge] [DecidableEq OtherEdge]

theorem pairResistance_reindex
    (network : Resistance.FiniteNetwork Vertex Edge) (other : Resistance.FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ≃ OtherVertex) (edges : Edge ≃ OtherEdge)
    (endpoint : ∀ edge, other.endpoint (edges edge) =
      (vertices (network.endpoint edge).1, vertices (network.endpoint edge).2))
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (first last : Vertex) :
    pairResistance other (fun edge => resistance (edges.symm edge)) (vertices first) (vertices last) =
      pairResistance network resistance first last := by
  have inverseEndpoint (edge : OtherEdge) : network.endpoint (edges.symm edge) =
      (vertices.symm (other.endpoint edge).1, vertices.symm (other.endpoint edge).2) := by
    have identity := endpoint (edges.symm edge)
    rw [Equiv.apply_symm_apply] at identity
    apply Prod.ext
    · exact (vertices.symm_apply_eq.mpr (congrArg Prod.fst identity)).symm
    · exact (vertices.symm_apply_eq.mpr (congrArg Prod.snd identity)).symm
  let forwardHom := networkEmbeddingGraphHom network other vertices.toEmbedding edges.toEmbedding endpoint
  let backwardHom := networkEmbeddingGraphHom other network vertices.symm.toEmbedding edges.symm.toEmbedding inverseEndpoint
  have forwardValues (vertex : Vertex) : forwardHom vertex = vertices vertex := rfl
  have backwardValues (vertex : OtherVertex) : backwardHom vertex = vertices.symm vertex := rfl
  by_cases distinct : first ≠ last
  · have otherDistinct : vertices first ≠ vertices last := fun equal => distinct (vertices.injective equal)
    by_cases reachable : network.graph.Reachable first last
    · have otherReach : other.graph.Reachable (vertices first) (vertices last) := by
        simpa only [forwardValues] using reachable.map forwardHom
      have conductance := effectiveConductance_reindex (retarget network first last distinct)
        (retarget other (vertices first) (vertices last) otherDistinct) vertices edges endpoint rfl rfl resistance
      rw [effectiveConductance_eq_reciprocalResistance _ otherReach (fun edge => positive _),
        effectiveConductance_eq_reciprocalResistance _ reachable positive] at conductance
      simp only [one_div] at conductance
      simpa only [pairResistance, dif_pos distinct, dif_pos otherDistinct] using inv_injective conductance
    · have otherUnreachable : ¬ other.graph.Reachable (vertices first) (vertices last) := by
        intro otherReach
        have mapped := otherReach.map backwardHom
        apply reachable
        simpa only [backwardValues, Equiv.symm_apply_apply] using mapped
      rw [pairResistance_eq_zero_of_unreachable other _ otherUnreachable,
        pairResistance_eq_zero_of_unreachable network _ reachable]
  · have equal := not_ne_iff.mp distinct
    subst last
    rw [pairResistance_self, pairResistance_self]

theorem terminalResistanceRadius_reindex
    (network : Resistance.FiniteNetwork Vertex Edge) (other : Resistance.FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ≃ OtherVertex) (edges : Edge ≃ OtherEdge)
    (endpoint : ∀ edge, other.endpoint (edges edge) =
      (vertices (network.endpoint edge).1, vertices (network.endpoint edge).2))
    (source : other.source = vertices network.source) (target : other.target = vertices network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) :
    terminalResistanceRadius other (fun edge => resistance (edges.symm edge)) =
      terminalResistanceRadius network resistance := by
  have valueIdentity (vertex : Vertex) :
      max (pairResistance other (fun edge => resistance (edges.symm edge)) other.source (vertices vertex))
        (pairResistance other (fun edge => resistance (edges.symm edge)) other.target (vertices vertex)) =
      max (pairResistance network resistance network.source vertex) (pairResistance network resistance network.target vertex) := by
    rw [source, target, pairResistance_reindex network other vertices edges endpoint resistance positive,
      pairResistance_reindex network other vertices edges endpoint resistance positive]
  apply le_antisymm
  · apply (Finset.sup'_le_iff _ _).mpr
    intro vertex _
    obtain ⟨previous, rfl⟩ := vertices.surjective vertex
    rw [valueIdentity]
    exact max_le (sourceResistance_le_radius network resistance previous) (targetResistance_le_radius network resistance previous)
  · apply (Finset.sup'_le_iff _ _).mpr
    intro vertex _
    rw [← valueIdentity]
    exact max_le (sourceResistance_le_radius other _ (vertices vertex)) (targetResistance_le_radius other _ (vertices vertex))

end
end IGSIII34.ResistanceLimit
