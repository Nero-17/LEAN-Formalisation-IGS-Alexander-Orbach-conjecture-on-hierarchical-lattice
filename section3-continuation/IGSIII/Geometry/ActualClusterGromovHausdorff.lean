import IGSIII.Geometry.ActualFiniteCluster
import IGSIII.Geometry.ActualChemicalNets

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter GromovHausdorff
open scoped Topology

theorem ghDist_le_of_embedded_anchor_distortion {Source Target Index : Type*}
    [MetricSpace Source] [CompactSpace Source] [Nonempty Source]
    [MetricSpace Target] [CompactSpace Target] [Nonempty Target]
    (embedding : Index ↪ Source) (limiting : Index → Target) (first_mesh error second_mesh : ℝ)
    (first_net : ∀ point : Source, ∃ anchor, dist point (embedding anchor) ≤ first_mesh)
    (second_net : ∀ point : Target, ∃ anchor, dist point (limiting anchor) ≤ second_mesh)
    (distortion : ∀ first last,
      |dist (embedding first) (embedding last) - dist (limiting first) (limiting last)| ≤ error) :
    ghDist Source Target ≤ first_mesh + error / 2 + second_mesh := by
  let matching : Set.range embedding → Target := fun point => limiting (Classical.choose point.property)
  have matching_identity (anchor : Index) : matching ⟨embedding anchor, ⟨anchor, rfl⟩⟩ = limiting anchor := by
    change limiting (Classical.choose (show ∃ other, embedding other = embedding anchor from ⟨anchor, rfl⟩)) = limiting anchor
    congr 1
    exact embedding.injective (Classical.choose_spec (show ∃ other, embedding other = embedding anchor from ⟨anchor, rfl⟩))
  apply ghDist_le_of_approx_subsets matching
  · intro point
    obtain ⟨anchor, close⟩ := first_net point
    exact ⟨embedding anchor, ⟨anchor, rfl⟩, close⟩
  · intro point
    obtain ⟨anchor, close⟩ := second_net point
    refine ⟨⟨embedding anchor, ⟨anchor, rfl⟩⟩, ?_⟩
    rw [matching_identity]
    exact close
  · intro first last
    change |dist first.val last.val - dist (matching first) (matching last)| ≤ error
    simpa only [matching, Classical.choose_spec first.property, Classical.choose_spec last.property] using
      distortion (Classical.choose first.property) (Classical.choose last.property)

theorem actualFiniteCluster_near_birth_skeleton (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_nonnegative : 0 ≤ eta) (coefficient_nonnegative : 0 ≤ coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (age depth : ℕ) (bound : age ≤ depth) (beyond : start ≤ age + 1)
    (point : ActualFiniteCluster rule configuration scale scale_positive depth) :
    ∃ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      dist point (retainedFiniteVertexEmbedding rule configuration coherent scale scale_positive age depth bound anchor) ≤
        coefficient * eta ^ (age + 1) := by
  classical
  have actual_reachable : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth [] true)).Reachable
        (plantedVertex (rule.generation depth).network true) point.val := by
    simpa only [← configuration_identity depth, plantedVertex, Bool.true_eq, ↓reduceIte] using point.property
  obtain ⟨fine_anchor, membership, fine_retained, close⟩ :=
    finite_skeleton_is_net_of_component_radius_bounds rule marks scale eta coefficient start scale_positive
      eta_nonnegative coefficient_nonnegative radius_bound depth age [] true true point.val (by simpa using beyond) actual_reachable
  rw [finiteSkeletonVertices_eq_persistent_image rule age depth bound] at membership
  obtain ⟨anchor, _, anchor_identity⟩ := Finset.mem_map.mp membership
  have retained_anchor : ((rule.generation age).network.openGraph (configuration age)).Reachable
      (rule.generation age).network.source anchor := by
    apply (persistentVertexEmbedding_reachable_iff rule configuration coherent age depth bound _ _).mp
    have source_identity := persistentVertexEmbedding_planted rule age depth bound true
    change persistentVertexEmbedding rule age depth bound (rule.generation age).network.source =
      (rule.generation depth).network.source at source_identity
    rw [source_identity, anchor_identity]
    simpa only [configuration_identity depth, plantedVertex, Bool.true_eq, ↓reduceIte] using fine_retained
  refine ⟨⟨anchor, retained_anchor⟩, ?_⟩
  change (((rule.generation depth).network.openGraph (configuration depth)).dist point.val
    (persistentVertexEmbedding rule age depth bound anchor) : ℝ) / scale ^ (depth + 1) ≤ _
  rw [anchor_identity]
  simpa only [← configuration_identity depth, List.length_nil, Nat.add_zero, Nat.zero_add, SimpleGraph.dist_comm] using close

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

/-- Actual finite full retained clusters converge in GH distance to the
constructed chemical completion. Both nets and all distortions are proved
from actual graph distances. -/
theorem actualFiniteCluster_ghDist_tendsto_zero_of_component_radius_bounds
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_nonnegative : 0 ≤ eta) (eta_lt_one : eta < 1)
    (coefficient_nonnegative : 0 ≤ coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length) :
    letI := actualChemicalSpace_compact_of_component_radius_bounds rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence marks configuration_identity eta coefficient start eta_nonnegative eta_lt_one
        coefficient_nonnegative radius_bound
    Tendsto (fun depth => ghDist (ActualFiniteCluster rule configuration scale scale_positive depth)
      (ActualChemicalSpace rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence))
        atTop (𝓝 0) := by
  letI := actualChemicalSpace_compact_of_component_radius_bounds rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence marks configuration_identity eta coefficient start eta_nonnegative eta_lt_one
      coefficient_nonnegative radius_bound
  have vanishing : Tendsto (fun age : ℕ => coefficient * eta ^ (age + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one eta_nonnegative eta_lt_one).comp (tendsto_add_atTop_nat 1))
  apply Metric.tendsto_atTop.mpr
  intro epsilon epsilon_positive
  obtain ⟨age, age_large, small_mesh⟩ := ((eventually_ge_atTop start).and
    ((tendsto_order.mp vanishing).2 (epsilon / 4) (by positivity))).exists
  have distortion_small : ∀ᶠ depth in atTop, ∀ first last : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      |persistentNormalizedDistance rule configuration scale age first.val last.val depth -
        dist (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age first)
          (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age last)| < epsilon := by
    apply Filter.eventually_all.mpr
    intro first
    apply Filter.eventually_all.mpr
    intro last
    have convergence := actual_persistent_skeleton_distances_tendsto rule classical configuration coherent scale scale_positive
      age (limit_length age) (child_convergence age) (first.property.symm.trans last.property)
    rw [← actualChemicalVertex_distance rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence
      age first last] at convergence
    exact (Metric.tendsto_nhds.mp convergence epsilon epsilon_positive).mono
      (fun _ close => by simpa only [Real.dist_eq] using close)
  obtain ⟨start_depth, bounds⟩ := eventually_atTop.mp ((eventually_ge_atTop age).and distortion_small)
  refine ⟨start_depth, fun depth depth_large => ?_⟩
  obtain ⟨age_bound, pair_bounds⟩ := bounds depth depth_large
  have gh_bound := ghDist_le_of_embedded_anchor_distortion
    (retainedFiniteVertexEmbedding rule configuration coherent scale scale_positive age depth age_bound)
    (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age)
    (coefficient * eta ^ (age + 1)) epsilon (coefficient * eta ^ (age + 1))
    (actualFiniteCluster_near_birth_skeleton rule configuration coherent scale scale_positive marks configuration_identity
      eta coefficient start eta_nonnegative coefficient_nonnegative radius_bound age depth age_bound (by omega))
    (actualChemicalSpace_near_birth_skeleton rule classical configuration coherent scale scale_positive limit_length nonnegative positive
      child_convergence marks configuration_identity eta coefficient start eta_nonnegative coefficient_nonnegative radius_bound age (by omega))
    (fun first last => by
      have close := (pair_bounds first last).le
      change |((((rule.generation depth).network.openGraph (configuration depth)).dist
          (persistentVertexEmbedding rule age depth age_bound first.val)
          (persistentVertexEmbedding rule age depth age_bound last.val) : ℝ) / scale ^ (depth + 1)) -
        dist (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age first)
          (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence age last)| ≤ epsilon
      simpa only [persistentNormalizedDistance, dif_pos age_bound] using close)
  have gh_nonnegative : 0 ≤ ghDist (ActualFiniteCluster rule configuration scale scale_positive depth)
      (ActualChemicalSpace rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence) := dist_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg gh_nonnegative]
  linarith

/-- A terminal-distance envelope, together with the concrete chemical
child-length limits, gives full-cluster GH convergence. No mesh, compactness,
metric compatibility, or GH certificate is an input. -/
theorem actualFiniteCluster_ghDist_tendsto_zero_of_terminal_envelope
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (scale_gt_one : 1 < scale) (eta : ℝ) (eta_positive : 0 < eta) (eta_lt_one : eta < 1)
    (growth_ge_one : 1 ≤ scale * eta) (start : ℕ)
    (terminal_envelope : ∀ address opened depth, start ≤ address.length →
      (markedTerminalDistance rule marks depth address opened : ℝ) / scale ^ (depth + 1) ≤
        (scale * eta) ^ address.length) :
    letI := actualChemicalSpace_compact_of_terminal_envelope rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence marks configuration_identity scale_gt_one eta eta_positive eta_lt_one
        growth_ge_one start terminal_envelope
    Tendsto (fun depth => ghDist (ActualFiniteCluster rule configuration scale scale_positive depth)
      (ActualChemicalSpace rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence))
        atTop (𝓝 0) := by
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
  apply actualFiniteCluster_ghDist_tendsto_zero_of_component_radius_bounds rule classical configuration coherent scale scale_positive
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

end
end IGSIII.Geometry
