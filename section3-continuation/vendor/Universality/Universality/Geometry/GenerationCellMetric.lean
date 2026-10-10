import Universality.Geometry.ScaledGenerationMetric
import Universality.Graph.GenerationCellEmbedding
import Universality.Graph.CellIsometry

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A first-level cell address is unchanged by the persistent old-vertex map. -/
theorem generationCellEmbedding_oldVertex (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (vertex : Fin (rule.generation depth).vertices) :
    rule.generationOldVertex (depth + 1)
        ((rule.generationCellEmbedding depth edge).vertex vertex) =
      (rule.generationCellEmbedding (depth + 1) edge).vertex
        (rule.generationOldVertex depth vertex) := by
  apply (rule.generationTopDecomposition (depth + 1)).vertex.injective
  change
    rule.network.substitutionAssociatorVertex (rule.generation depth).network rule.network
      (((rule.generationTopDecomposition depth).substitute
        (NetworkEquivalence.refl rule.network)).vertex
        (rule.generationOldVertex (depth + 1)
          ((rule.generationCellEmbedding depth edge).vertex vertex))) = _
  rw [show (((rule.generationTopDecomposition depth).substitute
      (NetworkEquivalence.refl rule.network)).vertex
      (rule.generationOldVertex (depth + 1)
        ((rule.generationCellEmbedding depth edge).vertex vertex))) =
      Fintype.equivFin _ (Sum.inl ((rule.generationTopDecomposition depth).vertex
        ((rule.generationCellEmbedding depth edge).vertex vertex))) from
    (rule.generationTopDecomposition depth).substituteVertex_old
      (NetworkEquivalence.refl rule.network) _]
  change rule.network.substitutionAssociatorVertex (rule.generation depth).network rule.network
    (Fintype.equivFin _ (Sum.inl ((rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm
        (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge vertex)))))) =
    (rule.generationTopDecomposition (depth + 1)).vertex
      ((rule.generationTopDecomposition (depth + 1)).vertex.symm
        (Fintype.equivFin _ (rule.network.cellVertex (rule.generation (depth + 1)).network edge
          (rule.generationOldVertex depth vertex))))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact rule.network.substitutionAssociator_coarse_cell (rule.generation depth).network
    rule.network edge vertex

theorem Classical.generationCellEmbedding_graph_distance {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (edge : Fin rule.edges) (first second : Fin (rule.generation depth).vertices) :
    (rule.generation (depth + 1)).network.fullGraph.dist
      ((rule.generationCellEmbedding depth edge).vertex first)
      ((rule.generationCellEmbedding depth edge).vertex second) =
      (rule.generation depth).network.fullGraph.dist first second := by
  have hreachable := ((h.generation (depth + 1)).connected
    ((rule.generationCellEmbedding depth edge).vertex first)).symm.trans
      ((h.generation (depth + 1)).connected
        ((rule.generationCellEmbedding depth edge).vertex second))
  have hisometry := graph_iso_distance_of_reachable
    ((rule.generationTopDecomposition depth).openGraphIso (fun _ => true)) hreachable
  have hcell := rule.network.substitute_cell_distance (rule.generation depth).network
    (h.generation depth).connected edge first second
  change (rule.network.substitute (rule.generation depth).network).fullGraph.dist
    ((rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm
        (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge first))))
    ((rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm
        (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge second)))) = _ at hisometry
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hisometry
  exact hisometry.symm.trans hcell

/-- Actual child cells contract the normalized graph distance by the reciprocal
of the terminal graph distance. -/
theorem Classical.generationCellEmbedding_scaled_distance {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (edge : Fin rule.edges) (first second : Fin (rule.generation depth).vertices) :
    scaledGenerationDistance rule (depth + 1)
        ((rule.generationCellEmbedding depth edge).vertex first)
        ((rule.generationCellEmbedding depth edge).vertex second) =
      (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) *
        scaledGenerationDistance rule depth first second := by
  dsimp only [scaledGenerationDistance]
  rw [h.generationCellEmbedding_graph_distance, pow_succ]
  field_simp [ne_of_gt h.scale_real_pos]

end
end Universality.Rule

