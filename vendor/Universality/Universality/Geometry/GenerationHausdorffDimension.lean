import Universality.Geometry.GenerationMetricCells
import Universality.Geometry.InternalSimilarity
import Universality.Geometry.SeparatedBlocks

/-! The actual compact metric limit has the Hausdorff dimension asserted in
the manuscript. The lower bound uses separated interior block copies and
therefore requires no uniform bound on vertex degrees. -/

namespace Universality.Rule
noncomputable section

/-- The Hausdorff dimension of the actual rescaled generation completion. -/
theorem generationMetricSpace_dimH_eq {rule : Rule} (h : rule.Classical) :
    dimH (Set.univ : Set (GenerationMetricSpace h)) = ENNReal.ofReal
      (Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by
  apply le_antisymm (generationMetricSpace_dimH_le h)
  obtain ⟨point, hpoint⟩ := generationMetricBoundaryDistance_pos_somewhere h
  have hcover : ∀ point : GenerationMetricSpace h,
      ∃ edge preimage, generationMetricCell h edge preimage = point := by
    intro point
    have hmem : point ∈ ⋃ edge, Set.range (generationMetricCell h edge) := by
      rw [generationMetricCell_cover h]
      exact Set.mem_univ point
    exact Set.mem_iUnion.mp hmem
  have hratio : 0 ≤ 1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) :=
    div_nonneg zero_le_one h.scale_real_pos.le
  have hratioOne : 1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) < 1 :=
    by simpa only [one_div] using (inv_lt_one₀ h.scale_real_pos).mpr (by exact_mod_cast h.scale)
  obtain ⟨depth, internal, margin, hmargin, hinternal_dist, hinternal_height⟩ :=
    Geometry.exists_internal_similarity (generationMetricCell h)
      (1 / (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ))
      hratio hratioOne (generationMetricCell_distance h) hcover
      (generationMetricBoundaryDistance h) (generationMetricBoundaryDistance_lipschitz h) point hpoint
  exact Geometry.SeparatedBlocks.integer_scale_dimension_le rule.edges
    (rule.network.fullGraph.dist rule.network.source rule.network.target) depth h.edges_gt_one h.scale
    (generationMetricCell h) (generationMetricBoundaryDistance h) margin hmargin
    (generationMetricCell_distance h) (generationMetricCell_boundary h)
    (generationMetricCell_separation h) internal hinternal_dist hinternal_height

end
end Universality.Rule

