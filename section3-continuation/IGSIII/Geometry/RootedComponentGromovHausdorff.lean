import IGSIII.Geometry.RootedFiniteComponent
import IGSIII.Geometry.RootedComponentCover
import IGSIII.Geometry.ActualClusterGromovHausdorff

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter GromovHausdorff
open scoped Topology
variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (address : List (Fin rule.edges)) (opened : Bool)
variable (configurationIdentity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth address opened)
variable (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ values depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < values depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + address.length)) atTop (𝓝 (values coarse edge)))

include opened configurationIdentity in
theorem rootedFiniteComponent_near_birth_skeleton
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (age depth : ℕ) (bound : age ≤ depth) (beyond : start ≤ address.length + age + 1)
    (point : RootedFiniteComponent rule configuration sourceSide scale scalePositive address.length depth) :
    ∃ anchor : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide,
      dist point (rootedFiniteVertexEmbedding rule configuration coherent sourceSide scale scalePositive address.length age depth bound anchor) ≤
        coefficient * eta ^ (address.length + age + 1) := by
  classical
  have actualReachable : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth address opened)).Reachable
        (plantedVertex (rule.generation depth).network sourceSide) point.val := by
    simpa only [← configurationIdentity depth] using point.property
  obtain ⟨fineAnchor, membership, fineRetained, close⟩ :=
    finite_skeleton_is_net_of_component_radius_bounds rule marks scale eta coefficient start scalePositive
      etaNonnegative coefficientNonnegative radiusBounds depth age address opened sourceSide point.val beyond actualReachable
  rw [finiteSkeletonVertices_eq_persistent_image rule age depth bound] at membership
  obtain ⟨anchor, _, anchorIdentity⟩ := Finset.mem_map.mp membership
  have retainedAnchor : ((rule.generation age).network.openGraph (configuration age)).Reachable
      (plantedVertex (rule.generation age).network sourceSide) anchor := by
    apply (persistentVertexEmbedding_reachable_iff rule configuration coherent age depth bound _ _).mp
    rw [persistentVertexEmbedding_planted, anchorIdentity]
    simpa only [configurationIdentity depth] using fineRetained
  refine ⟨⟨anchor, retainedAnchor⟩, ?_⟩
  change (((rule.generation depth).network.openGraph (configuration depth)).dist point.val
    (persistentVertexEmbedding rule age depth bound anchor) : ℝ) / scale ^ (depth + 1 + address.length) ≤ _
  rw [anchorIdentity]
  simpa only [← configurationIdentity depth, SimpleGraph.dist_comm] using close

include opened configurationIdentity in
/-- The actual finite component, including either side of a raw noncrossing
socket, converges to its intrinsic chemical completion in global units. -/
theorem rootedFiniteComponent_ghDist_tendsto_zero_of_component_radius_bounds
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length) :
    letI := rootedComponentSpace_compact_of_component_radius_bounds rule classicalRule configuration coherent sourceSide scale scalePositive
      marks address opened configurationIdentity values nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne
      coefficientNonnegative radiusBounds
    Tendsto (fun depth => ghDist (RootedFiniteComponent rule configuration sourceSide scale scalePositive address.length depth)
      (RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence)) atTop (𝓝 0) := by
  letI := rootedComponentSpace_compact_of_component_radius_bounds rule classicalRule configuration coherent sourceSide scale scalePositive
    marks address opened configurationIdentity values nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBounds
  have vanishing : Tendsto (fun age : ℕ => coefficient * eta ^ (address.length + age + 1)) atTop (𝓝 0) := by
    have powers := (tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp
      (tendsto_add_atTop_nat (address.length + 1))
    simpa only [Function.comp_apply, mul_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tendsto_const_nhds.mul powers
  apply Metric.tendsto_atTop.mpr
  intro epsilon epsilonPositive
  obtain ⟨age, ageLarge, smallMesh⟩ := ((eventually_ge_atTop start).and
    ((tendsto_order.mp vanishing).2 (epsilon / 4) (by positivity))).exists
  have distortionSmall : ∀ᶠ depth in atTop, ∀ first last : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide,
      |persistentNormalizedDistance rule configuration scale age first.val last.val depth / scale ^ address.length -
        dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length values nonnegative positive childConvergence age first)
          (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length values nonnegative positive childConvergence age last)| < epsilon := by
    apply Filter.eventually_all.mpr
    intro first
    apply Filter.eventually_all.mpr
    intro last
    have convergence := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule configuration coherent scale scalePositive
      address.length age values childConvergence (first.property.symm.trans last.property)
    rw [← rootedComponentVertex_distance rule classicalRule configuration coherent sourceSide scale scalePositive address.length
      values nonnegative positive childConvergence age first last] at convergence
    exact (Metric.tendsto_nhds.mp convergence epsilon epsilonPositive).mono
      (fun _ close => by simpa only [Real.dist_eq] using close)
  obtain ⟨startDepth, bounds⟩ := eventually_atTop.mp ((eventually_ge_atTop age).and distortionSmall)
  refine ⟨startDepth, fun depth depthLarge => ?_⟩
  obtain ⟨ageBound, pairBounds⟩ := bounds depth depthLarge
  have ghBound := ghDist_le_of_embedded_anchor_distortion
    (rootedFiniteVertexEmbedding rule configuration coherent sourceSide scale scalePositive address.length age depth ageBound)
    (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length values nonnegative positive childConvergence age)
    (coefficient * eta ^ (address.length + age + 1)) epsilon (coefficient * eta ^ (address.length + age + 1))
    (rootedFiniteComponent_near_birth_skeleton rule configuration coherent sourceSide scale scalePositive marks address opened configurationIdentity
      eta coefficient start etaNonnegative coefficientNonnegative radiusBounds age depth ageBound (by omega))
    (rootedComponentSpace_near_birth_skeleton rule classicalRule configuration coherent sourceSide scale scalePositive marks address opened configurationIdentity
      values nonnegative positive childConvergence eta coefficient start etaNonnegative coefficientNonnegative radiusBounds age (by omega))
    (fun first last => by
      have close := (pairBounds first last).le
      change |((((rule.generation depth).network.openGraph (configuration depth)).dist
          (persistentVertexEmbedding rule age depth ageBound first.val)
          (persistentVertexEmbedding rule age depth ageBound last.val) : ℝ) / scale ^ (depth + 1 + address.length)) -
        dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length values nonnegative positive childConvergence age first)
          (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length values nonnegative positive childConvergence age last)| ≤ epsilon
      simpa only [persistentNormalizedDistance, dif_pos ageBound, pow_add, div_div] using close)
  have ghNonnegative : 0 ≤ ghDist (RootedFiniteComponent rule configuration sourceSide scale scalePositive address.length depth)
      (RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive address.length values nonnegative positive childConvergence) := dist_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ghNonnegative]
  linarith

end
end IGSIII.Geometry
