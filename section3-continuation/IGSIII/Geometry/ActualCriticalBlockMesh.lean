import IGSIII.Geometry.ActualCriticalMesh
import IGSIII.Geometry.ActualBlockCellEmbedding

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology

/-- Every actual coarse-cell component is close to its own retained endpoint,
uniformly over all later microscopic graphs. B uses two separate anchors. -/
theorem exists_actual_critical_block_component_mesh (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ growth : ℝ,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∀ eta : ℝ, 0 < eta → eta < 1 → 1 < growth * eta →
        ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
          ∃ start : ℕ, ∀ coarse fine (edge : Fin (rule.generation coarse).edges) source_side
            (vertex : Fin (rule.generation fine).vertices), start ≤ coarse + 1 →
            ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
              (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
                (plantedVertex (rule.generation fine).network source_side) vertex →
            (((rule.generation (coarse + fine + 1)).network.openGraph
              (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
                ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network source_side))
                ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) : ℝ) /
              growth ^ (coarse + fine + 2) ≤ ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (coarse + 1) := by
  obtain ⟨growth, growth_lower, growth_upper, radius_bounds⟩ :=
    exists_actual_critical_uniform_component_mesh rule classicalRule p positive below_one fixed_point
  refine ⟨growth, growth_lower, growth_upper, ?_⟩
  intro eta eta_positive eta_lt_one product_gt_one
  have growth_positive : 0 < growth :=
    (show (0 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale).trans_le growth_lower
  filter_upwards [radius_bounds eta eta_positive eta_lt_one product_gt_one] with marks radius_bounds
  obtain ⟨start, radius_bounds⟩ := radius_bounds
  refine ⟨start, ?_⟩
  intro coarse fine edge source_side vertex beyond reachable
  have distance_bound := generationBlockCellEmbedding_distance_to_planted_le rule coarse fine edge
    (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) source_side vertex reachable
  have normalized := div_le_div_of_nonneg_right (show
      (((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
          ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network source_side))
          ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) : ℝ) ≤
        (terminalComponentRadius (rule.generation fine).network (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) : ℝ) by exact_mod_cast distance_bound)
    (pow_pos growth_positive (coarse + fine + 2)).le
  have cell_radius := radius_bounds (generationEdgeAddress rule coarse edge)
    (markedGenerationConfiguration rule marks coarse [] true edge) fine (by
      simpa only [generationEdgeAddress_length] using beyond)
  rw [generationEdgeAddress_length] at cell_radius
  have configuration_identity := generationBlockCells_marked rule marks coarse fine [] true edge
  simp only [List.nil_append] at configuration_identity
  rw [configuration_identity] at normalized
  exact normalized.trans (by
    simpa only [markedTerminalComponentRadius, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cell_radius)

end IGSIII.Geometry
