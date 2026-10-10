import IGSIII.Geometry.ActualSkeletonPersistence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

/-- Actual microscopic distances between the persistent coarse vertices. -/
noncomputable def persistentNormalizedDistance (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (coarse : ℕ) (first last : Fin (rule.generation coarse).vertices) (depth : ℕ) : ℝ :=
  if bound : coarse ≤ depth then
    (((rule.generation depth).network.openGraph (configuration depth)).dist
      (persistentVertexEmbedding rule coarse depth bound first)
      (persistentVertexEmbedding rule coarse depth bound last) : ℝ) / scale ^ (depth + 1)
  else 0

/-- The finite chemical skeleton distance is the limit of distances on the
same actual microscopic graph, once the actual block child lengths converge. -/
theorem actual_block_skeleton_distances_tendsto (rule : Rule) (classical : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale) (coarse : ℕ)
    (limit_length : Fin (rule.generation coarse).edges → ℝ)
    (child_convergence : ∀ edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length edge)))
    {first last : Fin (rule.generation coarse).vertices}
    (reachable : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable first last) :
    Tendsto (fun fine =>
      (((rule.generation (coarse + fine + 1)).network.openGraph (configuration (coarse + fine + 1))).dist
        (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last) : ℝ) /
      scale ^ (coarse + fine + 2)) atTop
        (𝓝 (weightedDistance ((rule.generation coarse).network.openGraph (configuration coarse))
          (indexedBondCost (rule.generation coarse).network limit_length) first last)) := by
  have convergence := actual_skeleton_distances_tendsto (rule.generation coarse).network
    (fun fine => (rule.generation fine).vertices) (fun fine => (rule.generation fine).edges)
    (fun fine => (rule.generation fine).network) (classical.generation coarse).simple
    (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)))
    (configuration coarse) (fun fine => generationBlockCoarse_of_coherent rule configuration coherent coarse fine)
    (fun fine => (scale ^ (coarse + fine + 2))⁻¹) (fun fine => inv_nonneg.mpr (pow_pos scale_positive _).le)
    limit_length (fun edge => by simpa only [div_eq_mul_inv, mul_comm] using child_convergence edge) reachable
  apply convergence.congr'
  apply Eventually.of_forall
  intro fine
  have transported := iso_distance_eq_all
    ((rule.generationBlockDecomposition coarse fine).openGraphIso (configuration (coarse + fine + 1)))
    (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last)
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
      ((rule.generationBlockDecomposition coarse fine).configuration (configuration (coarse + fine + 1)))).dist
        ((rule.generationBlockDecomposition coarse fine).vertex (blockOldVertexEmbedding rule coarse fine first))
        ((rule.generationBlockDecomposition coarse fine).vertex (blockOldVertexEmbedding rule coarse fine last)) = _ at transported
  have configuration_identity : (rule.generationBlockDecomposition coarse fine).configuration (configuration (coarse + fine + 1)) =
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine (configuration (coarse + fine + 1))) := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  rw [configuration_identity] at transported
  simp only [blockOldVertexEmbedding, Function.Embedding.coeFn_mk, Equiv.apply_symm_apply] at transported
  dsimp only
  rw [transported]
  simp only [div_eq_mul_inv, mul_comm, blockOldVertexEmbedding, Function.Embedding.coeFn_mk]

theorem persistentNormalizedDistance_transition (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (scale : ℝ)
    (coarse later : ℕ) (bound : coarse ≤ later)
    (first last : Fin (rule.generation coarse).vertices) :
    (fun depth => persistentNormalizedDistance rule configuration scale later
        (persistentVertexEmbedding rule coarse later bound first) (persistentVertexEmbedding rule coarse later bound last) depth)
      =ᶠ[atTop] persistentNormalizedDistance rule configuration scale coarse first last := by
  filter_upwards [eventually_ge_atTop later] with depth beyond
  simp only [persistentNormalizedDistance, dif_pos beyond, dif_pos (bound.trans beyond),
    persistentVertexEmbedding_trans]

theorem actual_persistent_skeleton_distances_tendsto (rule : Rule) (classical : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale) (coarse : ℕ)
    (limit_length : Fin (rule.generation coarse).edges → ℝ)
    (child_convergence : ∀ edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length edge)))
    {first last : Fin (rule.generation coarse).vertices}
    (reachable : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable first last) :
    Tendsto (persistentNormalizedDistance rule configuration scale coarse first last) atTop
      (𝓝 (weightedDistance ((rule.generation coarse).network.openGraph (configuration coarse))
        (indexedBondCost (rule.generation coarse).network limit_length) first last)) := by
  apply (tendsto_add_atTop_iff_nat (coarse + 1)).mp
  apply (actual_block_skeleton_distances_tendsto rule classical configuration coherent scale scale_positive
    coarse limit_length child_convergence reachable).congr'
  apply Eventually.of_forall
  intro fine
  dsimp only
  rw [show fine + (coarse + 1) = coarse + fine + 1 by omega]
  simp only [persistentNormalizedDistance, dif_pos (show coarse ≤ coarse + fine + 1 by omega)]
  rw [← blockOldVertexEmbedding_eq_persistent rule coarse fine first,
    ← blockOldVertexEmbedding_eq_persistent rule coarse fine last]

theorem persistentVertexEmbedding_next (rule : Rule) (depth : ℕ)
    (vertex : Fin (rule.generation depth).vertices) :
    persistentVertexEmbedding rule depth (depth + 1) (Nat.le_succ depth) vertex =
      rule.generationOldVertex depth vertex := by
  simp only [persistentVertexEmbedding, Universality.Geometry.IsometricSequence.transition,
    Function.Embedding.coeFn_mk, Nat.leRecOn_succ']

/-- Compatibility is proved from limits of the same actual microscopic
distances, rather than assumed as a metric-gluing certificate. -/
theorem actual_skeleton_weighted_distance_compatible (rule : Rule) (classical : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale)
    (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge)))
    (depth : ℕ) {first last : Fin (rule.generation depth).vertices}
    (reachable : ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last) :
    weightedDistance ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1)))
        (indexedBondCost (rule.generation (depth + 1)).network (limit_length (depth + 1)))
        (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
      weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
        (indexedBondCost (rule.generation depth).network (limit_length depth)) first last := by
  have later_reachable : ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
      (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) := by
    apply (rule.generation_reachable_old_iff depth (configuration (depth + 1)) first last).mpr
    rwa [coherent depth]
  have earlier_convergence := actual_persistent_skeleton_distances_tendsto rule classical configuration coherent
    scale scale_positive depth (limit_length depth) (child_convergence depth) reachable
  have later_convergence := actual_persistent_skeleton_distances_tendsto rule classical configuration coherent
    scale scale_positive (depth + 1) (limit_length (depth + 1)) (child_convergence (depth + 1)) later_reachable
  have same_distances := persistentNormalizedDistance_transition rule configuration scale depth (depth + 1)
    (Nat.le_succ depth) first last
  simp only [persistentVertexEmbedding_next] at same_distances
  exact tendsto_nhds_unique later_convergence (earlier_convergence.congr' same_distances.symm)

end IGSIII.Geometry
