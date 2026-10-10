import IGSIII.Geometry.CellLocalisationBlock
import IGSIII.Geometry.OffsetSkeletonCompatibility

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution Filter
open scoped Topology

/-- The actual boundary distance of a persistent cell point at microscopic
resolution, in the same global units as its intrinsic component metric. -/
def persistentNormalizedBoundaryDistance (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (offset fine : ℕ) (point : Fin (rule.generation fine).vertices) (host : ℕ) : ℝ :=
  if bound : fine ≤ host then
    componentBoundaryDistance ((rule.generation host).network.openGraph (configuration host))
      (rule.generation host).network.source (rule.generation host).network.target
      (persistentVertexEmbedding rule fine host bound point) / scale ^ (host + 1) / scale ^ offset
  else 0

theorem persistentNormalizedBoundaryDistance_identity (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (scale : ℝ) (scale_positive : 0 < scale)
    (offset fine host : ℕ) (bound : fine ≤ host) (point : Fin (rule.generation fine).vertices) :
    persistentNormalizedBoundaryDistance rule configuration scale offset fine point host =
      if ((rule.generation fine).network.openGraph (configuration fine)).Reachable (rule.generation fine).network.source point then
        if ((rule.generation fine).network.openGraph (configuration fine)).Reachable (rule.generation fine).network.target point then
          min (persistentNormalizedDistance rule configuration scale fine (rule.generation fine).network.source point host / scale ^ offset)
            (persistentNormalizedDistance rule configuration scale fine (rule.generation fine).network.target point host / scale ^ offset)
        else persistentNormalizedDistance rule configuration scale fine (rule.generation fine).network.source point host / scale ^ offset
      else if ((rule.generation fine).network.openGraph (configuration fine)).Reachable (rule.generation fine).network.target point then
        persistentNormalizedDistance rule configuration scale fine (rule.generation fine).network.target point host / scale ^ offset
      else 0 := by
  classical
  have source_reach := persistentVertexEmbedding_reachable_iff rule configuration coherent fine host bound
    (rule.generation fine).network.source point
  have target_reach := persistentVertexEmbedding_reachable_iff rule configuration coherent fine host bound
    (rule.generation fine).network.target point
  have source_identity := persistentVertexEmbedding_planted rule fine host bound true
  have target_identity := persistentVertexEmbedding_planted rule fine host bound false
  change persistentVertexEmbedding rule fine host bound (rule.generation fine).network.source =
    (rule.generation host).network.source at source_identity
  change persistentVertexEmbedding rule fine host bound (rule.generation fine).network.target =
    (rule.generation host).network.target at target_identity
  rw [source_identity] at source_reach
  rw [target_identity] at target_reach
  simp only [persistentNormalizedBoundaryDistance, dif_pos bound, componentBoundaryDistance,
    source_reach, target_reach, persistentNormalizedDistance, source_identity, target_identity]
  split_ifs
  · rw [min_div_div_right (pow_pos scale_positive offset).le,
      min_div_div_right (pow_pos scale_positive (host + 1)).le]
  · rfl
  · rfl
  · simp only [zero_div]

/-- Boundary distances converge from the same actual microscopic graph
metrics. Reachability of each terminal is kept fixed by coherent coarsening. -/
theorem actual_persistent_boundary_distances_tendsto (rule : Rule) (classicalRule : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale) (offset fine : ℕ)
    (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (child_convergence : ∀ coarse edge, Tendsto (fun depth =>
      (((rule.generation depth).network.openGraph
        (generationBlockCells rule coarse depth (configuration (coarse + depth + 1)) edge)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) /
        scale ^ (coarse + depth + 2 + offset)) atTop (𝓝 (values coarse edge)))
    (point : Fin (rule.generation fine).vertices) :
    Tendsto (persistentNormalizedBoundaryDistance rule configuration scale offset fine point) atTop
      (𝓝 (weightedComponentBoundaryDistance ((rule.generation fine).network.openGraph (configuration fine))
        (indexedBondCost (rule.generation fine).network (values fine))
        (rule.generation fine).network.source (rule.generation fine).network.target point)) := by
  classical
  by_cases source_reached : ((rule.generation fine).network.openGraph (configuration fine)).Reachable
      (rule.generation fine).network.source point <;>
    by_cases target_reached : ((rule.generation fine).network.openGraph (configuration fine)).Reachable
      (rule.generation fine).network.target point
  · have source_limit := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule configuration coherent
      scale scale_positive offset fine values child_convergence source_reached
    have target_limit := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule configuration coherent
      scale scale_positive offset fine values child_convergence target_reached
    simp only [weightedComponentBoundaryDistance, if_pos source_reached, if_pos target_reached]
    apply (source_limit.min target_limit).congr'
    filter_upwards [eventually_ge_atTop fine] with host beyond
    rw [persistentNormalizedBoundaryDistance_identity rule configuration coherent scale scale_positive offset fine host beyond,
      if_pos source_reached, if_pos target_reached]
  · have source_limit := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule configuration coherent
      scale scale_positive offset fine values child_convergence source_reached
    simp only [weightedComponentBoundaryDistance, if_pos source_reached, if_neg target_reached]
    apply source_limit.congr'
    filter_upwards [eventually_ge_atTop fine] with host beyond
    rw [persistentNormalizedBoundaryDistance_identity rule configuration coherent scale scale_positive offset fine host beyond,
      if_pos source_reached, if_neg target_reached]
  · have target_limit := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule configuration coherent
      scale scale_positive offset fine values child_convergence target_reached
    simp only [weightedComponentBoundaryDistance, if_neg source_reached, if_pos target_reached]
    apply target_limit.congr'
    filter_upwards [eventually_ge_atTop fine] with host beyond
    rw [persistentNormalizedBoundaryDistance_identity rule configuration coherent scale scale_positive offset fine host beyond,
      if_neg source_reached, if_pos target_reached]
  · simp only [weightedComponentBoundaryDistance, if_neg source_reached, if_neg target_reached]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop fine] with host beyond
    rw [persistentNormalizedBoundaryDistance_identity rule configuration coherent scale scale_positive offset fine host beyond,
      if_neg source_reached, if_neg target_reached]

end
end IGSIII.Geometry
