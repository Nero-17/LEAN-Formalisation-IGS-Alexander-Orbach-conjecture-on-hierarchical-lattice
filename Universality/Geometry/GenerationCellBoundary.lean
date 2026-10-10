import Universality.Geometry.CellBoundaryPotential
import Universality.Geometry.GenerationCellMetric

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)

theorem exists_cellVertex_of_connected
    (houter : ∀ vertex, outer.fullGraph.Reachable outer.source vertex)
    (vertex : outer.SubstitutionVertex inner) :
    ∃ edge point, outer.cellVertex inner edge point = vertex := by
  classical
  rcases vertex with vertex | ⟨edge, point⟩
  · have hneighbor : (outer.fullGraph.neighborSet vertex).Nonempty := by
      by_cases hsource : vertex = outer.source
      · subst vertex
        exact (houter outer.target).nonempty_neighborSet_left outer.terminals_distinct
      · exact (houter vertex).nonempty_neighborSet_right (Ne.symm hsource)
    obtain ⟨neighbor, hneighbor⟩ := hneighbor
    obtain ⟨_, edge, _, hpair | hpair⟩ := hneighbor
    · refine ⟨edge, inner.source, ?_⟩
      rw [outer.cellVertex_source]
      exact congrArg Sum.inl (congrArg Prod.fst hpair)
    · refine ⟨edge, inner.target, ?_⟩
      rw [outer.cellVertex_target]
      exact congrArg Sum.inl (congrArg Prod.snd hpair)
  · exact ⟨edge, point.val, outer.cellVertex_eq_interior inner edge point⟩

variable {outer inner}

theorem NetworkEquivalence.fullGraph_distance
    (equivalence : outer.NetworkEquivalence inner)
    (houter : ∀ vertex, outer.fullGraph.Reachable outer.source vertex)
    (first second : Fin outerVertices) :
    inner.fullGraph.dist (equivalence.vertex first) (equivalence.vertex second) =
      outer.fullGraph.dist first second :=
  graph_iso_distance_of_reachable (equivalence.openGraphIso (fun _ => true))
    ((houter first).symm.trans (houter second))

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem Classical.generation_exists_cell_vertex {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (vertex : Fin (rule.generation (depth + 1)).vertices) :
    ∃ edge point, (rule.generationCellEmbedding depth edge).vertex point = vertex := by
  obtain ⟨edge, point, hpoint⟩ := rule.network.exists_cellVertex_of_connected
    (rule.generation depth).network h.connected
    ((Fintype.equivFin _).symm ((rule.generationTopDecomposition depth).vertex vertex))
  refine ⟨edge, point, ?_⟩
  apply (rule.generationTopDecomposition depth).vertex.injective
  change (rule.generationTopDecomposition depth).vertex
    ((rule.generationTopDecomposition depth).vertex.symm
      (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge point))) = _
  rw [Equiv.apply_symm_apply, hpoint, Equiv.apply_symm_apply]

def scaledGenerationBoundaryDistance (rule : Rule) (depth : ℕ)
    (vertex : Fin (rule.generation depth).vertices) : ℝ :=
  (rule.generation depth).network.boundaryDistance vertex /
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1)

theorem Classical.scaledGenerationBoundaryDistance_eq {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    scaledGenerationBoundaryDistance rule depth vertex =
      min (scaledGenerationDistance rule depth (rule.generation depth).network.source vertex)
        (scaledGenerationDistance rule depth (rule.generation depth).network.target vertex) := by
  exact (min_div_div_right (pow_nonneg h.scale_real_pos.le _) _ _).symm

theorem Classical.generationCellEmbedding_boundary_distance {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (edge : Fin rule.edges) (vertex : Fin (rule.generation depth).vertices) :
    (rule.generation depth).network.boundaryDistance vertex ≤
      (rule.generation (depth + 1)).network.boundaryDistance
        ((rule.generationCellEmbedding depth edge).vertex vertex) := by
  have hsource := rule.network.substitute_cell_boundary_le_distance_to_old
    (rule.generation depth).network h.connected (h.generation depth).connected edge vertex rule.network.source
  have htarget := rule.network.substitute_cell_boundary_le_distance_to_old
    (rule.generation depth).network h.connected (h.generation depth).connected edge vertex rule.network.target
  have hdistance (old : Fin (rule.generation (depth + 1)).vertices) :=
    (rule.generationTopDecomposition depth).fullGraph_distance (h.generation (depth + 1)).connected
      ((rule.generationCellEmbedding depth edge).vertex vertex) old
  have hsourceDistance := hdistance (rule.generation (depth + 1)).network.source
  have htargetDistance := hdistance (rule.generation (depth + 1)).network.target
  change (rule.network.substitute (rule.generation depth).network).fullGraph.dist
    ((rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm (Fintype.equivFin _
        (rule.network.cellVertex (rule.generation depth).network edge vertex)))) _ = _ at hsourceDistance htargetDistance
  rw [Equiv.apply_symm_apply, (rule.generationTopDecomposition depth).source] at hsourceDistance
  rw [Equiv.apply_symm_apply, (rule.generationTopDecomposition depth).target] at htargetDistance
  change (rule.generation depth).network.boundaryDistance vertex ≤ min _ _
  apply le_min
  · have transported := hsource.trans_eq (congrArg (fun value : ℕ => (value : ℝ)) hsourceDistance)
    simpa only [SimpleGraph.dist_comm] using transported
  · have transported := htarget.trans_eq (congrArg (fun value : ℕ => (value : ℝ)) htargetDistance)
    simpa only [SimpleGraph.dist_comm] using transported

theorem Classical.generationCellEmbedding_scaled_boundary {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (edge : Fin rule.edges) (vertex : Fin (rule.generation depth).vertices) :
    (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) *
        scaledGenerationBoundaryDistance rule depth vertex ≤
      scaledGenerationBoundaryDistance rule (depth + 1)
        ((rule.generationCellEmbedding depth edge).vertex vertex) := by
  have hbound := h.generationCellEmbedding_boundary_distance depth edge vertex
  dsimp only [scaledGenerationBoundaryDistance]
  rw [pow_succ]
  calc
    _ = (rule.generation depth).network.boundaryDistance vertex /
        ((rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1) *
          (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (mul_nonneg (pow_nonneg h.scale_real_pos.le _) h.scale_real_pos.le)

theorem Classical.generationCellEmbedding_scaled_separation {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (first second : Fin rule.edges) (hdistinct : first ≠ second)
    (u v : Fin (rule.generation depth).vertices) :
    (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) *
        (scaledGenerationBoundaryDistance rule depth u + scaledGenerationBoundaryDistance rule depth v) ≤
      scaledGenerationDistance rule (depth + 1)
        ((rule.generationCellEmbedding depth first).vertex u)
        ((rule.generationCellEmbedding depth second).vertex v) := by
  have hbound := rule.network.substitute_distinct_cell_boundary_separation
    (rule.generation depth).network h.connected (h.generation depth).connected first second hdistinct u v
  have hdistance := (rule.generationTopDecomposition depth).fullGraph_distance
    (h.generation (depth + 1)).connected
    ((rule.generationCellEmbedding depth first).vertex u)
    ((rule.generationCellEmbedding depth second).vertex v)
  change (rule.network.substitute (rule.generation depth).network).fullGraph.dist
    ((rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm (Fintype.equivFin _
        (rule.network.cellVertex (rule.generation depth).network first u))))
    ((rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm (Fintype.equivFin _
        (rule.network.cellVertex (rule.generation depth).network second v)))) = _ at hdistance
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hdistance
  rw [hdistance] at hbound
  dsimp only [scaledGenerationBoundaryDistance, scaledGenerationDistance]
  rw [pow_succ]
  calc
    _ = ((rule.generation depth).network.boundaryDistance u + (rule.generation depth).network.boundaryDistance v) /
        ((rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1) *
          (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (mul_nonneg (pow_nonneg h.scale_real_pos.le _) h.scale_real_pos.le)

end
end Universality.Rule

