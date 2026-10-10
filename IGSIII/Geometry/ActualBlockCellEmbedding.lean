import IGSIII.Geometry.ActualSkeletonPersistence
import IGSIII.Chemical.SubstitutionPaths.BlockAddresses

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- The actual indexed descendant network inside a fixed coarse edge. -/
def generationBlockCellEmbedding (rule : Rule) (coarse fine : ℕ) (edge : Fin (rule.generation coarse).edges) :
    (rule.generation fine).network.NetworkEmbedding (rule.generation (coarse + fine + 1)).network :=
  ((rule.generation coarse).network.cellNetworkEmbedding (rule.generation fine).network edge).trans
    (NetworkEmbedding.ofEquivalence (rule.generationBlockDecomposition coarse fine).symm)

theorem generationBlockCellEmbedding_restrict (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges) :
    (generationBlockCellEmbedding rule coarse fine edge).restrict configuration =
      generationBlockCells rule coarse fine configuration edge := rfl

theorem generationBlockCellEmbedding_source (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges) :
    (generationBlockCellEmbedding rule coarse fine edge).vertex (rule.generation fine).network.source =
      blockOldVertexEmbedding rule coarse fine ((rule.generation coarse).network.endpoint edge).1 := by
  change (rule.generationBlockDecomposition coarse fine).vertex.symm
    (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge (rule.generation fine).network.source)) = _
  rw [(rule.generation coarse).network.cellVertex_source]
  rfl

theorem generationBlockCellEmbedding_target (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges) :
    (generationBlockCellEmbedding rule coarse fine edge).vertex (rule.generation fine).network.target =
      blockOldVertexEmbedding rule coarse fine ((rule.generation coarse).network.endpoint edge).2 := by
  change (rule.generationBlockDecomposition coarse fine).vertex.symm
    (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge (rule.generation fine).network.target)) = _
  rw [(rule.generation coarse).network.cellVertex_target]
  rfl

/-- Block cell embeddings commute with the genuine persistent old-vertex
maps, so fixed cell points define points of the same directed skeleton. -/
theorem generationBlockCellEmbedding_next (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges) (vertex : Fin (rule.generation fine).vertices) :
    rule.generationOldVertex (coarse + fine + 1) ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) =
      (generationBlockCellEmbedding rule coarse (fine + 1) edge).vertex (rule.generationOldVertex fine vertex) := by
  apply (rule.generationBlockDecomposition coarse (fine + 1)).vertex.injective
  change (rule.generation coarse).network.substitutionAssociatorVertex (rule.generation fine).network rule.network
    (((rule.generationBlockDecomposition coarse fine).substitute (NetworkEquivalence.refl rule.network)).vertex
      (rule.generationOldVertex (coarse + fine + 1) ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex))) = _
  rw [show (((rule.generationBlockDecomposition coarse fine).substitute (NetworkEquivalence.refl rule.network)).vertex
      (rule.generationOldVertex (coarse + fine + 1) ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex))) =
      Fintype.equivFin _ (Sum.inl ((rule.generationBlockDecomposition coarse fine).vertex
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex))) from
    (rule.generationBlockDecomposition coarse fine).substituteVertex_old (NetworkEquivalence.refl rule.network) _]
  change (rule.generation coarse).network.substitutionAssociatorVertex (rule.generation fine).network rule.network
    (Fintype.equivFin _ (Sum.inl ((rule.generationBlockDecomposition coarse fine).vertex
      ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge vertex)))))) =
    (rule.generationBlockDecomposition coarse (fine + 1)).vertex
      ((rule.generationBlockDecomposition coarse (fine + 1)).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation (fine + 1)).network edge
          (rule.generationOldVertex fine vertex))))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (rule.generation coarse).network.substitutionAssociator_coarse_cell (rule.generation fine).network rule.network edge vertex

theorem generationBlockCellEmbedding_persistent (rule : Rule) (coarse fine host : ℕ)
    (bound : fine ≤ host) (edge : Fin (rule.generation coarse).edges) (vertex : Fin (rule.generation fine).vertices) :
    persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) =
      (generationBlockCellEmbedding rule coarse host edge).vertex (persistentVertexEmbedding rule fine host bound vertex) := by
  induction host, bound using Nat.le_induction with
  | base =>
      simp only [persistentVertexEmbedding, Universality.Geometry.IsometricSequence.transition,
        Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ host bound induction_hypothesis =>
      change Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
        (show coarse + fine + 1 ≤ (coarse + host + 1) + 1 by omega)
        (fun {depth} => rule.generationOldVertex depth)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) =
          (generationBlockCellEmbedding rule coarse (host + 1) edge).vertex
            (Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
              (show fine ≤ host + 1 by omega) (fun {depth} => rule.generationOldVertex depth) vertex)
      rw [Nat.leRecOn_succ (show coarse + fine + 1 ≤ coarse + host + 1 by omega), Nat.leRecOn_succ bound]
      change rule.generationOldVertex (coarse + host + 1)
        (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
          ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex)) = _
      rw [induction_hypothesis, generationBlockCellEmbedding_next]
      rfl

theorem generationBlockCellEmbedding_openGraphHom_apply (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (vertex : Fin (rule.generation fine).vertices) :
    (generationBlockCellEmbedding rule coarse fine edge).openGraphHom configuration vertex =
      (generationBlockCellEmbedding rule coarse fine edge).vertex vertex := rfl

theorem generationBlockCellEmbedding_distance_le (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (first last : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable first last) :
    ((rule.generation (coarse + fine + 1)).network.openGraph configuration).dist
      ((generationBlockCellEmbedding rule coarse fine edge).vertex first)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex last) ≤
        ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).dist first last := by
  obtain ⟨walk, length⟩ := reachable.exists_walk_length_eq_dist
  have bound : ((rule.generation (coarse + fine + 1)).network.openGraph configuration).dist
      ((generationBlockCellEmbedding rule coarse fine edge).vertex first)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex last) ≤ walk.length := by
    simpa only [SimpleGraph.Walk.length_map, generationBlockCellEmbedding_openGraphHom_apply] using
      SimpleGraph.dist_le (walk.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom configuration))
  rwa [length] at bound

theorem generationBlockCellEmbedding_distance_to_planted_le (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (source_side : Bool) (vertex : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
      (plantedVertex (rule.generation fine).network source_side) vertex) :
    ((rule.generation (coarse + fine + 1)).network.openGraph configuration).dist
      ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network source_side))
      ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) ≤
        terminalComponentRadius (rule.generation fine).network (generationBlockCells rule coarse fine configuration edge) := by
  apply (generationBlockCellEmbedding_distance_le rule coarse fine edge configuration _ _ reachable).trans
  cases source_side with
  | false => exact target_distance_le_terminalComponentRadius _ _ vertex
  | true => exact source_distance_le_terminalComponentRadius _ _ vertex

end
end IGSIII.Geometry
