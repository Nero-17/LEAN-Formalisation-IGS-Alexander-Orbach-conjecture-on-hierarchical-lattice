import IGSIII34.ResistanceLimit.ActualChemicalJointAnchorCompletion20261011
import IGSIII34.Topology.JointAnchorDistortionCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5600000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

variable (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < lengths depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
        (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

include crossing

/-- The projection of every retained finite vertex to its actual chemical
birth vertex has vanishing distortion uniformly over all vertex pairs.
It is proved from original microscopic mesh bounds and fixed-skeleton
chemical distance limits, and does not assert the projection is isometric. -/
theorem actual_chemical_birth_uniform_distortion_completion20261011
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ first last :
      ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth,
      |dist first last - dist
        (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence depth first)
        (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence depth last)| < tolerance := by
  have meshVanish : Tendsto (fun coarse : ℕ => coefficient*eta^(coarse+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp
        (tendsto_add_atTop_nat 1)).const_mul coefficient)
  obtain ⟨coarse, beyond, meshSmall⟩ :=
    ((eventually_ge_atTop start).and
      (meshVanish.eventually (gt_mem_nhds (by positivity : (0:ℝ) < tolerance/8)))).exists
  have anchorSmall : ∀ᶠ depth in atTop, ∀ first last :
      RetainedSkeletonVertex (rule.generation coarse).network (markedGenerationConfiguration rule marks coarse [] true),
      |persistentNormalizedDistance rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          scale coarse first.val last.val depth - dist
        (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence coarse first)
        (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence coarse last)| < tolerance/2 := by
    apply Filter.eventually_all.mpr
    intro first
    apply Filter.eventually_all.mpr
    intro last
    have convergence := actual_persistent_skeleton_distances_tendsto rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive
      coarse (lengths coarse) (childConvergence coarse) (first.property.symm.trans last.property)
    rw [← actualChemicalVertex_distance rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
      nonnegative positive childConvergence coarse first last] at convergence
    exact (Metric.tendsto_nhds.mp convergence (tolerance/2) (by positivity)).mono
      (fun _ close => by simpa only [Real.dist_eq] using close)
  obtain ⟨threshold, largeBounds⟩ := eventually_atTop.mp anchorSmall
  refine eventually_atTop.mpr ⟨max threshold (coarse+1), ?_⟩
  intro depth large first last
  obtain ⟨fine, depthIdentity⟩ : ∃ fine : ℕ, depth = coarse+fine+1 :=
    ⟨depth-coarse-1, by omega⟩
  subst depth
  have anchorBounds := largeBounds (coarse+fine+1) (by omega)
  let projection := actualChemicalVertex rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
    nonnegative positive childConvergence (coarse+fine+1)
  have fullBound := IGSIII34.Topology.joint_anchor_projection_distortion_completion20261011
    (retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive coarse (coarse+fine+1) (by omega))
    (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive lengths nonnegative positive childConvergence coarse)
    projection (coefficient*eta^(coarse+1)) (coefficient*eta^(coarse+1)) (tolerance/2)
    (actual_chemical_finite_birth_joint_anchor_completion20261011 rule classicalRule marks crossing coherent
      scale scalePositive lengths nonnegative positive childConvergence eta coefficient start radiusBounds coarse fine beyond)
    (fun first last => by
      have small := (anchorBounds first last).le
      change |(((rule.generation (coarse+fine+1)).network.openGraph
          (markedGenerationConfiguration rule marks (coarse+fine+1) [] true)).dist
          (persistentVertexEmbedding rule coarse (coarse+fine+1) (by omega) first.val)
          (persistentVertexEmbedding rule coarse (coarse+fine+1) (by omega) last.val) : ℝ) /
          scale^(coarse+fine+1+1) - _| ≤ tolerance/2
      simpa only [persistentNormalizedDistance, dif_pos (by omega : coarse ≤ coarse+fine+1)] using small)
    first last
  exact fullBound.trans_lt (by linarith)

end
end IGSIII34.ResistanceLimit
