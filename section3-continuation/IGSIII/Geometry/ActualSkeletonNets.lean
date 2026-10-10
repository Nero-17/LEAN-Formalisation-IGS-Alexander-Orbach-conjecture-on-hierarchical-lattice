import IGSIII.Geometry.ActualSkeletonVertices
import IGSIII.Geometry.UniformComponentMesh

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped ENNReal Topology

variable {vertices edges : ℕ}

theorem planted_distance_le_terminalComponentRadius (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (source_side : Bool) (vertex : Fin vertices) :
    (network.openGraph configuration).dist (plantedVertex network source_side) vertex ≤ terminalComponentRadius network configuration := by
  cases source_side
  · exact target_distance_le_terminalComponentRadius network configuration vertex
  · exact source_distance_le_terminalComponentRadius network configuration vertex

theorem generationCellEmbedding_planted_mem_finiteSkeleton (rule : Rule) (depth age : ℕ)
    (edge : Fin rule.edges) (source_side : Bool) :
    (rule.generationCellEmbedding depth edge).vertex (plantedVertex (rule.generation depth).network source_side) ∈
      finiteSkeletonVertices rule (depth + 1) age := by
  cases source_side
  · change (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.target ∈ _
    rw [generationCellEmbedding_target]
    exact oldVertex_mem_finiteSkeleton rule depth age _
  · change (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.source ∈ _
    rw [generationCellEmbedding_source]
    exact oldVertex_mem_finiteSkeleton rule depth age _

theorem normalized_markedChild_distance_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) (edge : Fin rule.edges)
    (first last : Fin (rule.generation depth).vertices)
    (reachable : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).Reachable first last)
    (scale : ℝ) (scale_positive : 0 < scale) :
    (((rule.generation (depth + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (depth + 1) address opened)).dist
        ((rule.generationCellEmbedding depth edge).vertex first) ((rule.generationCellEmbedding depth edge).vertex last) : ℝ) /
          scale ^ (depth + 1 + 1 + address.length) ≤
    (((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).dist first last : ℝ) /
        scale ^ (depth + 1 + (address ++ [edge]).length) := by
  have distance_bound := markedChild_distance_le rule marks depth address opened edge first last reachable
  have cast_bound : (((rule.generation (depth + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (depth + 1) address opened)).dist
        ((rule.generationCellEmbedding depth edge).vertex first) ((rule.generationCellEmbedding depth edge).vertex last) : ℝ) ≤
    (((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).dist first last : ℝ) := by
    exact_mod_cast distance_bound
  have lengths : depth + 1 + 1 + address.length = depth + 1 + (address ++ [edge]).length := by simp; omega
  rw [lengths]
  exact div_le_div_of_nonneg_right cast_bound (pow_pos scale_positive _).le

/-- Actual birth skeletons are nets in every later full retained component.
The proof follows available child terminals, including dangling branches and
the original separate B components, through the actual cell embeddings. -/
theorem finite_skeleton_is_net_of_component_radius_bounds (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (scale eta coefficient : ℝ) (start : ℕ)
    (scale_positive : 0 < scale) (eta_nonnegative : 0 ≤ eta) (coefficient_nonnegative : 0 ≤ coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length) :
    ∀ depth age address opened source_side (vertex : Fin (rule.generation depth).vertices),
      start ≤ address.length + age + 1 →
      ((rule.generation depth).network.openGraph
        (markedGenerationConfiguration rule marks depth address opened)).Reachable
          (plantedVertex (rule.generation depth).network source_side) vertex →
      ∃ anchor ∈ finiteSkeletonVertices rule depth age,
        ((rule.generation depth).network.openGraph
          (markedGenerationConfiguration rule marks depth address opened)).Reachable
            (plantedVertex (rule.generation depth).network source_side) anchor ∧
        (((rule.generation depth).network.openGraph
          (markedGenerationConfiguration rule marks depth address opened)).dist anchor vertex : ℝ) /
            scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ (address.length + age + 1) := by
  intro depth
  induction depth with
  | zero =>
    intro age address opened source_side vertex _ reachable
    refine ⟨vertex, Finset.mem_univ _, reachable, ?_⟩
    simp only [SimpleGraph.dist_self, Nat.cast_zero, zero_div]
    exact mul_nonneg coefficient_nonnegative (pow_nonneg eta_nonnegative _)
  | succ depth induction_hypothesis =>
    intro age address opened source_side vertex beyond reachable
    rcases retained_generation_point_old_or_child rule marks depth address opened source_side vertex reachable with
      ⟨old, vertex_identity⟩ | ⟨edge, child, child_side, vertex_identity, child_reachable, terminal_retained⟩
    · refine ⟨vertex, ?_, reachable, ?_⟩
      · rw [vertex_identity]
        exact oldVertex_mem_finiteSkeleton rule depth age old
      · simp only [SimpleGraph.dist_self, Nat.cast_zero, zero_div]
        exact mul_nonneg coefficient_nonnegative (pow_nonneg eta_nonnegative _)
    · cases age with
      | zero =>
        refine ⟨(rule.generationCellEmbedding depth edge).vertex (plantedVertex (rule.generation depth).network child_side),
          generationCellEmbedding_planted_mem_finiteSkeleton rule depth 0 edge child_side, terminal_retained, ?_⟩
        rw [vertex_identity]
        apply (normalized_markedChild_distance_le rule marks depth address opened edge _ _ child_reachable scale scale_positive).trans
        have child_beyond : start ≤ (address ++ [edge]).length := by simp; omega
        have local_bound := (div_le_div_of_nonneg_right
          (show (((rule.generation depth).network.openGraph
            (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).dist
              (plantedVertex (rule.generation depth).network child_side) child : ℝ) ≤
              (markedTerminalComponentRadius rule marks depth (address ++ [edge]) (marks (address, opened) edge) : ℝ) by
                exact_mod_cast planted_distance_le_terminalComponentRadius (rule.generation depth).network _ child_side child)
          (pow_pos scale_positive (depth + 1 + (address ++ [edge]).length)).le).trans
            (radius_bound (address ++ [edge]) (marks (address, opened) edge) depth child_beyond)
        simpa only [List.length_append, List.length_singleton, Nat.add_zero] using local_bound
      | succ age =>
        have child_beyond : start ≤ (address ++ [edge]).length + age + 1 := by simp; omega
        obtain ⟨child_anchor, membership, child_anchor_retained, child_close⟩ := induction_hypothesis age (address ++ [edge])
          (marks (address, opened) edge) child_side child child_beyond child_reachable
        refine ⟨(rule.generationCellEmbedding depth edge).vertex child_anchor,
          childVertex_mem_finiteSkeleton rule depth age edge child_anchor membership, ?_, ?_⟩
        · have mapped := child_anchor_retained.map (markedChildHom rule marks depth address opened edge)
          simp only [markedChildHom_vertex] at mapped
          exact terminal_retained.trans mapped
        · rw [vertex_identity]
          have embedded_bound := normalized_markedChild_distance_le rule marks depth address opened edge child_anchor child
            (child_anchor_retained.symm.trans child_reachable) scale scale_positive
          apply embedded_bound.trans
          simpa only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using child_close

/-- The actual retained cluster admits its actual finite birth skeleton as an
exponentially fine net, uniformly in every later generation. The only random
input is a moment bound for a terminal-distance envelope. -/
theorem ae_actual_cluster_skeleton_nets (rule : Rule)
    (probability : Measure (((List (Fin rule.edges) × Bool) → Configuration rule.edges)))
    (scale eta : ℝ) (scale_gt_one : 1 < scale) (eta_positive : 0 < eta) (eta_lt_one : eta < 1)
    (growth_ge_one : 1 ≤ scale * eta)
    (power : ℕ) (power_positive : 0 < power) (moment_growth : (rule.edges : ℝ) < (scale * eta) ^ power)
    (envelope : List (Fin rule.edges) → Bool →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (measurable : ∀ address opened, AEStronglyMeasurable (envelope address opened) probability)
    (bound : ℝ≥0∞) (bound_finite : bound ≠ ∞)
    (moment_bound : ∀ address opened, eLpNorm (envelope address opened) power probability ≤ bound)
    (terminal_bound : ∀ᵐ marks ∂probability, ∀ address opened depth,
      (markedTerminalDistance rule marks depth address opened : ℝ) / scale ^ (depth + 1) ≤
        envelope address opened marks) :
    ∀ᵐ marks ∂probability, ∃ start : ℕ, ∀ age depth opened source_side
      (vertex : Fin (rule.generation depth).vertices), start ≤ age + 1 →
      ((rule.generation depth).network.openGraph
        (markedGenerationConfiguration rule marks depth [] opened)).Reachable
          (plantedVertex (rule.generation depth).network source_side) vertex →
      ∃ anchor ∈ finiteSkeletonVertices rule depth age,
        ((rule.generation depth).network.openGraph
          (markedGenerationConfiguration rule marks depth [] opened)).Reachable
            (plantedVertex (rule.generation depth).network source_side) anchor ∧
        (((rule.generation depth).network.openGraph
          (markedGenerationConfiguration rule marks depth [] opened)).dist anchor vertex : ℝ) /
            scale ^ (depth + 1) ≤ ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (age + 1) := by
  have radius_bounds := ae_uniform_actual_component_mesh rule probability scale eta scale_gt_one eta_positive
    eta_lt_one growth_ge_one power power_positive moment_growth envelope measurable bound bound_finite moment_bound terminal_bound
  filter_upwards [radius_bounds] with marks radius_bounds
  obtain ⟨start, radius_bounds⟩ := radius_bounds
  refine ⟨start, ?_⟩
  intro age depth opened source_side vertex beyond reachable
  have coefficient_nonnegative : 0 ≤ (rule.edges + 1 : ℝ) / (1 - eta) :=
    div_nonneg (by positivity) (sub_pos.mpr eta_lt_one).le
  have skeleton_net := finite_skeleton_is_net_of_component_radius_bounds rule marks scale eta
    ((rule.edges + 1 : ℝ) / (1 - eta)) start (zero_lt_one.trans scale_gt_one) eta_positive.le
    coefficient_nonnegative radius_bounds depth age [] opened source_side vertex (by simpa using beyond) reachable
  simpa only [List.length_nil, Nat.add_zero, Nat.zero_add] using skeleton_net

end IGSIII.Geometry
