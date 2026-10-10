import IGSIII.Geometry.ActualChemicalSkeleton
import IGSIII.Geometry.ActualBirthSkeletonPersistence
import IGSIII.Geometry.SkeletonCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

variable (rule : Rule) (classical : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scale_positive : 0 < scale)
variable (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < limit_length depth edge)
variable (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge)))

/-- The microscopic full-cluster nets pass to the constructed chemical metric
by convergence on each fixed finite skeleton. The anchor is selected from the
actual retained earlier generation, not from an assumed limiting net. -/
theorem actualChemicalVertex_near_birth_skeleton
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_nonnegative : 0 ≤ eta) (coefficient_nonnegative : 0 ≤ coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (age depth : ℕ) (bound : age ≤ depth) (beyond : start ≤ age + 1)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    ∃ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      dist (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence depth vertex)
        (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age anchor) ≤
          coefficient * eta ^ (age + 1) := by
  classical
  by_contra no_anchor
  have all_far : ∀ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      coefficient * eta ^ (age + 1) <
        dist (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence depth vertex)
          (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age anchor) := by
    intro anchor
    exact lt_of_not_ge (fun close => no_anchor ⟨anchor, close⟩)
  have eventually_far (anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age)) :
      ∀ᶠ host in atTop, coefficient * eta ^ (age + 1) <
        persistentNormalizedDistance rule configuration scale depth vertex.val
          (persistentVertexEmbedding rule age depth bound anchor.val) host := by
    have convergence := actual_persistent_skeleton_distances_tendsto rule classical configuration coherent scale scale_positive
      depth (limit_length depth) (child_convergence depth)
      (vertex.property.symm.trans (retainedPersistentVertexEmbedding rule configuration coherent age depth bound anchor).property)
    simp only [retainedPersistentVertexEmbedding_val] at convergence
    have limit_identity :
        dist (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence depth vertex)
          (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age anchor) =
        weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
          (indexedBondCost (rule.generation depth).network (limit_length depth)) vertex.val
            (persistentVertexEmbedding rule age depth bound anchor.val) := by
      rw [actualChemicalVertex_persistent rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence
        age depth bound anchor, actualChemicalVertex_distance]
      rfl
    rw [← limit_identity] at convergence
    exact (tendsto_order.mp convergence).1 _ (all_far anchor)
  have uniformly_far := (Filter.eventually_all.mpr eventually_far)
  obtain ⟨host, host_large, all_far_host⟩ := ((eventually_ge_atTop depth).and uniformly_far).exists
  have retained_host := (retainedPersistentVertexEmbedding rule configuration coherent depth host host_large vertex).property
  have actual_net := finite_skeleton_is_net_of_component_radius_bounds rule marks scale eta coefficient start scale_positive
    eta_nonnegative coefficient_nonnegative radius_bound host age [] true true
      (persistentVertexEmbedding rule depth host host_large vertex.val) (by simpa using beyond)
  have actual_reachable : ((rule.generation host).network.openGraph
      (markedGenerationConfiguration rule marks host [] true)).Reachable
        (plantedVertex (rule.generation host).network true) (persistentVertexEmbedding rule depth host host_large vertex.val) := by
    simpa only [retainedPersistentVertexEmbedding_val, ← configuration_identity host, plantedVertex, Bool.true_eq, ↓reduceIte] using retained_host
  obtain ⟨fine_anchor, membership, fine_retained, close⟩ := actual_net actual_reachable
  rw [finiteSkeletonVertices_eq_persistent_image rule age host (bound.trans host_large)] at membership
  obtain ⟨anchor, _, anchor_identity⟩ := Finset.mem_map.mp membership
  have retained_anchor : ((rule.generation age).network.openGraph (configuration age)).Reachable
      (rule.generation age).network.source anchor := by
    apply (persistentVertexEmbedding_reachable_iff rule configuration coherent age host (bound.trans host_large) _ _).mp
    have source_identity := persistentVertexEmbedding_planted rule age host (bound.trans host_large) true
    change persistentVertexEmbedding rule age host (bound.trans host_large) (rule.generation age).network.source =
      (rule.generation host).network.source at source_identity
    rw [source_identity, anchor_identity]
    simpa only [configuration_identity host, plantedVertex, Bool.true_eq, ↓reduceIte] using fine_retained
  have far := all_far_host ⟨anchor, retained_anchor⟩
  simp only [persistentNormalizedDistance, dif_pos host_large, persistentVertexEmbedding_trans] at far
  rw [anchor_identity] at far
  have close_actual :
      (((rule.generation host).network.openGraph (configuration host)).dist
        (persistentVertexEmbedding rule depth host host_large vertex.val) fine_anchor : ℝ) /
        scale ^ (host + 1) ≤ coefficient * eta ^ (age + 1) := by
    simpa only [← configuration_identity host, List.length_nil, Nat.add_zero, Nat.zero_add, SimpleGraph.dist_comm] using close
  exact (not_lt_of_ge close_actual) far

/-- Compactness follows from the proved actual birth nets and their geometric
mesh. The realization itself is the completion already constructed above. -/
theorem actualChemicalSpace_compact_of_component_radius_bounds
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_nonnegative : 0 ≤ eta) (eta_lt_one : eta < 1)
    (coefficient_nonnegative : 0 ≤ coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length) :
    CompactSpace (ActualChemicalSpace rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence) := by
  classical
  have vanishing : Tendsto (fun age : ℕ => coefficient * eta ^ (age + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one eta_nonnegative eta_lt_one).comp (tendsto_add_atTop_nat 1))
  have bounded : TotallyBounded (⋃ depth, Set.range (actualChemicalVertex rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence depth)) := by
    apply Metric.totallyBounded_iff.mpr
    intro epsilon epsilon_positive
    have eventually_small := (tendsto_order.mp vanishing).2 epsilon epsilon_positive
    obtain ⟨age, age_large, small⟩ := ((eventually_ge_atTop start).and eventually_small).exists
    refine ⟨Set.range (actualChemicalVertex rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence age), Set.finite_range _, ?_⟩
    intro point membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    rcases le_total age depth with bound | bound
    · obtain ⟨anchor, close⟩ := actualChemicalVertex_near_birth_skeleton rule classical configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence marks configuration_identity eta coefficient start eta_nonnegative
        coefficient_nonnegative radius_bound age depth bound (by omega) vertex
      exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨anchor, rfl⟩, close.trans_lt small⟩⟩
    · refine Set.mem_iUnion.mpr ⟨actualChemicalVertex rule classical configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence age
          (retainedPersistentVertexEmbedding rule configuration coherent depth age bound vertex),
        Set.mem_iUnion.mpr ⟨⟨_, rfl⟩, ?_⟩⟩
      rw [← actualChemicalVertex_persistent rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence
        depth age bound vertex]
      exact Metric.mem_ball_self epsilon_positive
  have compact := bounded.closure.isCompact_of_isClosed isClosed_closure
  rw [(actualChemicalVertex_dense rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence).closure_eq] at compact
  exact isCompact_univ_iff.mp compact

/-- The genuine terminal-distance envelope suffices for compactness. Actual
component radii and full retained-cluster nets are derived in the proof. -/
theorem actualChemicalSpace_compact_of_terminal_envelope
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (scale_gt_one : 1 < scale) (eta : ℝ) (eta_positive : 0 < eta) (eta_lt_one : eta < 1)
    (growth_ge_one : 1 ≤ scale * eta) (start : ℕ)
    (terminal_envelope : ∀ address opened depth, start ≤ address.length →
      (markedTerminalDistance rule marks depth address opened : ℝ) / scale ^ (depth + 1) ≤
        (scale * eta) ^ address.length) :
    CompactSpace (ActualChemicalSpace rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence) := by
  have coefficient_nonnegative : 0 ≤ (rule.edges + 1 : ℝ) / (1 - eta) :=
    div_nonneg (by positivity) (sub_pos.mpr eta_lt_one).le
  have coefficient_large : (rule.edges : ℝ) ≤ (rule.edges + 1 : ℝ) / (1 - eta) := by
    apply (le_div_iff₀ (sub_pos.mpr eta_lt_one)).mpr
    nlinarith [show (0 : ℝ) ≤ (rule.edges : ℝ) from Nat.cast_nonneg _]
  have coefficient_contracts : eta * ((rule.edges + 1 : ℝ) / (1 - eta) + rule.edges) ≤
      (rule.edges + 1 : ℝ) / (1 - eta) := by
    have formula : ((rule.edges + 1 : ℝ) / (1 - eta)) * (1 - eta) = rule.edges + 1 :=
      div_mul_cancel₀ _ (sub_pos.mpr eta_lt_one).ne'
    have edges_bound : eta * rule.edges ≤ (rule.edges : ℝ) :=
      mul_le_of_le_one_left (Nat.cast_nonneg _) eta_lt_one.le
    nlinarith
  have radius_bounds := marked_radius_uniform_bound_of_terminal_envelope rule marks scale eta
    ((rule.edges + 1 : ℝ) / (1 - eta)) start scale_gt_one eta_positive growth_ge_one coefficient_large coefficient_contracts
    (fun address opened depth beyond => by
      simpa only [mul_comm] using (div_le_iff₀ (pow_pos scale_positive (depth + 1))).mp
        (terminal_envelope address opened depth beyond))
  apply actualChemicalSpace_compact_of_component_radius_bounds rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence marks configuration_identity eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
    eta_positive.le eta_lt_one coefficient_nonnegative
  intro address opened depth beyond
  calc
    _ ≤ (((rule.edges + 1 : ℝ) / (1 - eta)) * scale ^ (depth + 1) * (scale * eta) ^ address.length) /
        scale ^ (depth + 1 + address.length) :=
      div_le_div_of_nonneg_right (radius_bounds depth address opened beyond) (pow_pos scale_positive _).le
    _ = _ := by
      rw [pow_add, mul_pow]
      field_simp [scale_positive.ne']
      ring

theorem actualChemicalSpace_near_birth_skeleton
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_nonnegative : 0 ≤ eta) (coefficient_nonnegative : 0 ≤ coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (age : ℕ) (beyond : start ≤ age + 1)
    (point : ActualChemicalSpace rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence) :
    ∃ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      dist point (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age anchor) ≤
        coefficient * eta ^ (age + 1) := by
  have cover_closed : IsClosed (⋃ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      Metric.closedBall (actualChemicalVertex rule classical configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence age anchor) (coefficient * eta ^ (age + 1))) :=
    isClosed_iUnion_of_finite (fun _ => Metric.isClosed_closedBall)
  have cover_vertices : (⋃ depth, Set.range (actualChemicalVertex rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence depth)) ⊆
      ⋃ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
        Metric.closedBall (actualChemicalVertex rule classical configuration coherent scale scale_positive
          limit_length nonnegative positive child_convergence age anchor) (coefficient * eta ^ (age + 1)) := by
    intro vertex membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    rcases le_total age depth with bound | bound
    · obtain ⟨anchor, close⟩ := actualChemicalVertex_near_birth_skeleton rule classical configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence marks configuration_identity eta coefficient start eta_nonnegative
        coefficient_nonnegative radius_bound age depth bound beyond vertex
      exact Set.mem_iUnion.mpr ⟨anchor, close⟩
    · refine Set.mem_iUnion.mpr ⟨retainedPersistentVertexEmbedding rule configuration coherent depth age bound vertex, ?_⟩
      rw [← actualChemicalVertex_persistent rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence
        depth age bound vertex]
      exact Metric.mem_closedBall_self (mul_nonneg coefficient_nonnegative (pow_nonneg eta_nonnegative _))
  have cover_completion := closure_minimal cover_vertices cover_closed
  rw [(actualChemicalVertex_dense rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence).closure_eq] at cover_completion
  obtain ⟨anchor, close⟩ := Set.mem_iUnion.mp (cover_completion (Set.mem_univ point))
  exact ⟨anchor, Metric.mem_closedBall.mp close⟩

end
end IGSIII.Geometry
