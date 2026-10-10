import IGSIII.Geometry.RootedComponentPersistence
import IGSIII.Geometry.ActualSkeletonNets
import IGSIII.Geometry.ActualBirthSkeletonPersistence

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
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
theorem rootedComponentVertex_near_birth_skeleton
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (age depth : ℕ) (bound : age ≤ depth) (beyond : start ≤ address.length + age + 1)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    ∃ anchor : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide,
      dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence depth vertex)
        (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
          values nonnegative positive childConvergence age anchor) ≤ coefficient * eta ^ (address.length + age + 1) := by
  classical
  by_contra noAnchor
  have allFar : ∀ anchor : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide,
      coefficient * eta ^ (address.length + age + 1) <
        dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
          values nonnegative positive childConvergence depth vertex)
          (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
            values nonnegative positive childConvergence age anchor) := by
    intro anchor
    exact lt_of_not_ge (fun close => noAnchor ⟨anchor, close⟩)
  have eventuallyFar (anchor : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide) :
      ∀ᶠ host in atTop, coefficient * eta ^ (address.length + age + 1) <
        persistentNormalizedDistance rule configuration scale depth vertex.val
          (persistentVertexEmbedding rule age depth bound anchor.val) host / scale ^ address.length := by
    have convergence := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule configuration coherent scale scalePositive
      address.length depth values childConvergence
      (vertex.property.symm.trans (retainedComponentPersistentEmbedding rule configuration coherent sourceSide age depth bound anchor).property)
    have limitIdentity :
        dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
          values nonnegative positive childConvergence depth vertex)
          (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
            values nonnegative positive childConvergence age anchor) =
        weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
          (indexedBondCost (rule.generation depth).network (values depth)) vertex.val
            (persistentVertexEmbedding rule age depth bound anchor.val) := by
      rw [rootedComponentVertex_persistent rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence age depth bound anchor, rootedComponentVertex_distance]
      rfl
    simp only [retainedComponentPersistentEmbedding_val] at convergence
    change Tendsto (fun host => persistentNormalizedDistance rule configuration scale depth vertex.val
      (persistentVertexEmbedding rule age depth bound anchor.val) host / scale ^ address.length) _ _ at convergence
    rw [← limitIdentity] at convergence
    exact (tendsto_order.mp convergence).1 _ (allFar anchor)
  obtain ⟨host, hostLarge, allFarHost⟩ := ((eventually_ge_atTop depth).and (Filter.eventually_all.mpr eventuallyFar)).exists
  have retainedHost := (retainedComponentPersistentEmbedding rule configuration coherent sourceSide depth host hostLarge vertex).property
  have actualReachable : ((rule.generation host).network.openGraph (markedGenerationConfiguration rule marks host address opened)).Reachable
      (plantedVertex (rule.generation host).network sourceSide) (persistentVertexEmbedding rule depth host hostLarge vertex.val) := by
    simpa only [← configurationIdentity host, retainedComponentPersistentEmbedding_val] using retainedHost
  obtain ⟨fineAnchor, membership, fineRetained, close⟩ := finite_skeleton_is_net_of_component_radius_bounds rule marks scale eta coefficient start
    scalePositive etaNonnegative coefficientNonnegative radiusBounds host age address opened sourceSide
      (persistentVertexEmbedding rule depth host hostLarge vertex.val) beyond actualReachable
  rw [finiteSkeletonVertices_eq_persistent_image rule age host (bound.trans hostLarge)] at membership
  obtain ⟨anchor, _, anchorIdentity⟩ := Finset.mem_map.mp membership
  have retainedAnchor : ((rule.generation age).network.openGraph (configuration age)).Reachable
      (plantedVertex (rule.generation age).network sourceSide) anchor := by
    apply (persistentVertexEmbedding_reachable_iff rule configuration coherent age host (bound.trans hostLarge) _ _).mp
    rw [persistentVertexEmbedding_planted, anchorIdentity]
    simpa only [configurationIdentity host] using fineRetained
  have far := allFarHost ⟨anchor, retainedAnchor⟩
  simp only [persistentNormalizedDistance, dif_pos hostLarge, persistentVertexEmbedding_trans] at far
  rw [anchorIdentity] at far
  have closeActual :
      (((rule.generation host).network.openGraph (configuration host)).dist
        (persistentVertexEmbedding rule depth host hostLarge vertex.val) fineAnchor : ℝ) /
        scale ^ (host + 1) / scale ^ address.length ≤ coefficient * eta ^ (address.length + age + 1) := by
    simpa only [← configurationIdentity host, pow_add, div_div, SimpleGraph.dist_comm] using close
  exact (not_lt_of_ge closeActual) far

include opened configurationIdentity in
theorem rootedComponentSpace_compact_of_component_radius_bounds
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length) :
    CompactSpace (RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive address.length
      values nonnegative positive childConvergence) := by
  classical
  have vanishing : Tendsto (fun age : ℕ => coefficient * eta ^ (address.length + age + 1)) atTop (𝓝 0) := by
    have powers := (tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp
      ((tendsto_add_atTop_nat (address.length + 1)))
    simpa only [Function.comp_apply, mul_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tendsto_const_nhds.mul powers
  have bounded : TotallyBounded (⋃ depth, Set.range (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
      values nonnegative positive childConvergence depth)) := by
    apply Metric.totallyBounded_iff.mpr
    intro epsilon epsilonPositive
    obtain ⟨age, ageLarge, small⟩ := ((eventually_ge_atTop start).and ((tendsto_order.mp vanishing).2 epsilon epsilonPositive)).exists
    refine ⟨Set.range (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
      values nonnegative positive childConvergence age), Set.finite_range _, ?_⟩
    intro point membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    rcases le_total age depth with bound | bound
    · obtain ⟨anchor, close⟩ := rootedComponentVertex_near_birth_skeleton rule classicalRule configuration coherent sourceSide scale scalePositive
        marks address opened configurationIdentity values nonnegative positive childConvergence eta coefficient start etaNonnegative coefficientNonnegative
        radiusBounds age depth bound (by omega) vertex
      exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨anchor, rfl⟩, close.trans_lt small⟩⟩
    · refine Set.mem_iUnion.mpr ⟨rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence age (retainedComponentPersistentEmbedding rule configuration coherent sourceSide depth age bound vertex),
        Set.mem_iUnion.mpr ⟨⟨_, rfl⟩, ?_⟩⟩
      rw [← rootedComponentVertex_persistent rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence depth age bound vertex]
      exact Metric.mem_ball_self epsilonPositive
  have compact := bounded.closure.isCompact_of_isClosed isClosed_closure
  rw [(rootedComponentVertex_dense rule classicalRule configuration coherent sourceSide scale scalePositive address.length
    values nonnegative positive childConvergence).closure_eq] at compact
  exact isCompact_univ_iff.mp compact

end
end IGSIII.Geometry

