import Universality.Geometry.GenerationMetricSpace
import Universality.Geometry.GenerationCellBoundary
import Universality.Geometry.SequenceSimilarity

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NNReal

def generationMetricCell {rule : Rule} (h : rule.Classical) (edge : Fin rule.edges) :
    GenerationMetricSpace h → GenerationMetricSpace h := by
  letI (depth : ℕ) := scaledGenerationMetricSpace h depth
  exact Geometry.IsometricSequence.completionCell
    (fun depth => Fin (rule.generation depth).vertices) rule.generationOldVertex
    (fun depth => (rule.generationCellEmbedding depth edge).vertex)
    (fun depth => rule.generationCellEmbedding_oldVertex depth edge)
    (fun depth => h.generationOldVertex_isometry depth)

theorem generationMetricCell_vertex {rule : Rule} (h : rule.Classical) (edge : Fin rule.edges)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    generationMetricCell h edge (generationMetricVertex h depth vertex) =
      generationMetricVertex h (depth + 1) ((rule.generationCellEmbedding depth edge).vertex vertex) := by
  letI (depth : ℕ) := scaledGenerationMetricSpace h depth
  exact Geometry.IsometricSequence.completionCell_mk
    (fun depth => Fin (rule.generation depth).vertices) rule.generationOldVertex
    (fun depth => (rule.generationCellEmbedding depth edge).vertex)
    (fun depth => rule.generationCellEmbedding_oldVertex depth edge)
    (fun depth => h.generationOldVertex_isometry depth)
    ⟨1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ),
      div_nonneg zero_le_one h.scale_real_pos.le⟩
    (fun depth first second => h.generationCellEmbedding_scaled_distance depth edge first second)
    depth vertex

theorem generationMetricCell_distance {rule : Rule} (h : rule.Classical) (edge : Fin rule.edges)
    (first second : GenerationMetricSpace h) :
    dist (generationMetricCell h edge first) (generationMetricCell h edge second) =
      (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) * dist first second := by
  letI (depth : ℕ) := scaledGenerationMetricSpace h depth
  exact Geometry.IsometricSequence.completionCell_dist
    (fun depth => Fin (rule.generation depth).vertices) rule.generationOldVertex
    (fun depth => (rule.generationCellEmbedding depth edge).vertex)
    (fun depth => rule.generationCellEmbedding_oldVertex depth edge)
    (fun depth => h.generationOldVertex_isometry depth)
    ⟨1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ),
      div_nonneg zero_le_one h.scale_real_pos.le⟩
    (fun depth first second => h.generationCellEmbedding_scaled_distance depth edge first second)
    first second

theorem generationMetricCell_continuous {rule : Rule} (h : rule.Classical) (edge : Fin rule.edges) :
    Continuous (generationMetricCell h edge) := by
  have hlipschitz : LipschitzWith
      ⟨1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ),
        div_nonneg zero_le_one h.scale_real_pos.le⟩ (generationMetricCell h edge) :=
    LipschitzWith.of_dist_le_mul (fun first second => (generationMetricCell_distance h edge first second).le)
  exact hlipschitz.continuous

theorem generationMetricCell_cover {rule : Rule} (h : rule.Classical) :
    (⋃ edge, Set.range (generationMetricCell h edge)) = Set.univ := by
  have hclosed : IsClosed (⋃ edge, Set.range (generationMetricCell h edge)) :=
    isClosed_iUnion_of_finite (fun edge => (isCompact_range (generationMetricCell_continuous h edge)).isClosed)
  have hsubset : (⋃ depth, Set.range (generationMetricVertex h depth)) ⊆
      ⋃ edge, Set.range (generationMetricCell h edge) := by
    intro point hpoint
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp hpoint
    obtain ⟨edge, child, hchild⟩ := h.generation_exists_cell_vertex depth (rule.generationOldVertex depth vertex)
    refine Set.mem_iUnion.mpr ⟨edge, generationMetricVertex h depth child, ?_⟩
    rw [generationMetricCell_vertex, hchild, ← generationMetricVertex_old]
  have hclosure := closure_minimal hsubset hclosed
  rw [(generationMetricVertex_dense h).closure_eq] at hclosure
  exact Set.eq_univ_of_subset hclosure rfl

def generationMetricBoundaryDistance {rule : Rule} (h : rule.Classical)
    (point : GenerationMetricSpace h) : ℝ :=
  min (dist (generationMetricVertex h 0 rule.network.source) point)
    (dist (generationMetricVertex h 0 rule.network.target) point)

theorem generationMetricVertex_source {rule : Rule} (h : rule.Classical) (depth : ℕ) :
    generationMetricVertex h depth (rule.generation depth).network.source =
      generationMetricVertex h 0 rule.network.source := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    exact (generationMetricVertex_old h depth (rule.generation depth).network.source).symm.trans ih

theorem generationMetricVertex_target {rule : Rule} (h : rule.Classical) (depth : ℕ) :
    generationMetricVertex h depth (rule.generation depth).network.target =
      generationMetricVertex h 0 rule.network.target := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    exact (generationMetricVertex_old h depth (rule.generation depth).network.target).symm.trans ih

theorem generationMetricBoundaryDistance_vertex {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    generationMetricBoundaryDistance h (generationMetricVertex h depth vertex) =
      scaledGenerationBoundaryDistance rule depth vertex := by
  dsimp only [generationMetricBoundaryDistance]
  rw [← generationMetricVertex_source h depth, ← generationMetricVertex_target h depth,
    generationMetricVertex_distance, generationMetricVertex_distance]
  exact (h.scaledGenerationBoundaryDistance_eq depth vertex).symm

theorem generationMetricBoundaryDistance_lipschitz {rule : Rule} (h : rule.Classical) :
    LipschitzWith 1 (generationMetricBoundaryDistance h) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [NNReal.coe_one, one_mul]
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le
    (dist_dist_dist_le_right (generationMetricVertex h 0 rule.network.source) first second)
    (dist_dist_dist_le_right (generationMetricVertex h 0 rule.network.target) first second))

theorem generationMetricBoundaryDistance_nonneg {rule : Rule} (h : rule.Classical)
    (point : GenerationMetricSpace h) : 0 ≤ generationMetricBoundaryDistance h point :=
  le_min dist_nonneg dist_nonneg

theorem generationMetricBoundaryDistance_pos_somewhere {rule : Rule} (h : rule.Classical) :
    ∃ point : GenerationMetricSpace h, 0 < generationMetricBoundaryDistance h point := by
  obtain ⟨vertex, hsource, htarget⟩ := Fin.exists_ne_and_ne_of_two_lt
    rule.network.source rule.network.target h.vertices_gt_two
  refine ⟨generationMetricVertex h 0 vertex, ?_⟩
  rw [generationMetricBoundaryDistance_vertex]
  apply div_pos _ (pow_pos h.scale_real_pos _)
  apply lt_min
  · exact_mod_cast Nat.pos_of_ne_zero (fun hzero => hsource ((h.connected vertex).dist_eq_zero_iff.mp hzero).symm)
  · exact_mod_cast Nat.pos_of_ne_zero (fun hzero => htarget
      (((h.connected rule.network.target).symm.trans (h.connected vertex)).dist_eq_zero_iff.mp hzero).symm)

theorem generationMetricCell_boundary {rule : Rule} (h : rule.Classical) (edge : Fin rule.edges)
    (point : GenerationMetricSpace h) :
    (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) *
        generationMetricBoundaryDistance h point ≤
      generationMetricBoundaryDistance h (generationMetricCell h edge point) := by
  have hboundary := (generationMetricBoundaryDistance_lipschitz h).continuous
  refine UniformSpace.Completion.induction_on point
    (isClosed_le (continuous_const.mul hboundary)
      (hboundary.comp (generationMetricCell_continuous h edge))) ?_
  intro point
  obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk
    (Geometry.IsometricSequence.transition (fun depth => Fin (rule.generation depth).vertices)
      rule.generationOldVertex) point
  change _ * generationMetricBoundaryDistance h (generationMetricVertex h depth vertex) ≤
    generationMetricBoundaryDistance h (generationMetricCell h edge (generationMetricVertex h depth vertex))
  rw [generationMetricCell_vertex, generationMetricBoundaryDistance_vertex, generationMetricBoundaryDistance_vertex]
  exact h.generationCellEmbedding_scaled_boundary depth edge vertex

theorem generationMetricCell_separation {rule : Rule} (h : rule.Classical)
    (first second : Fin rule.edges) (hdistinct : first ≠ second)
    (x y : GenerationMetricSpace h) :
    (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) *
        (generationMetricBoundaryDistance h x + generationMetricBoundaryDistance h y) ≤
      dist (generationMetricCell h first x) (generationMetricCell h second y) := by
  have hboundary := (generationMetricBoundaryDistance_lipschitz h).continuous
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_le
      (continuous_const.mul ((hboundary.comp continuous_fst).add (hboundary.comp continuous_snd)))
      (((generationMetricCell_continuous h first).comp continuous_fst).dist
        ((generationMetricCell_continuous h second).comp continuous_snd))) ?_
  intro x y
  obtain ⟨depth, u, v, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂
    (Geometry.IsometricSequence.transition (fun depth => Fin (rule.generation depth).vertices)
      rule.generationOldVertex) x y
  change _ * (generationMetricBoundaryDistance h (generationMetricVertex h depth u) +
      generationMetricBoundaryDistance h (generationMetricVertex h depth v)) ≤
    dist (generationMetricCell h first (generationMetricVertex h depth u))
      (generationMetricCell h second (generationMetricVertex h depth v))
  rw [generationMetricCell_vertex, generationMetricCell_vertex, generationMetricBoundaryDistance_vertex,
    generationMetricBoundaryDistance_vertex, generationMetricVertex_distance]
  exact h.generationCellEmbedding_scaled_separation depth first second hdistinct u v

end
end Universality.Rule

