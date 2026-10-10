import IGSIII.Geometry.UniformComponentMesh

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {vertices edges : ℕ}

/-- Distances within any actual selected component are controlled by its
terminal radius. The two components of B are never joined artificially. -/
theorem selected_component_distance_le_twice_radius (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (source_selected target_selected : Bool)
    (first last : Fin vertices)
    (selected : network.selectedActive source_selected target_selected configuration first = true)
    (same_component : (network.openGraph configuration).Reachable first last) :
    (network.openGraph configuration).dist first last ≤ 2 * terminalComponentRadius network configuration := by
  simp only [selectedActive, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true] at selected
  rcases selected with ⟨_, reachable⟩ | ⟨_, reachable⟩
  · have triangle := reachable.symm.dist_triangle_left last
    rw [show (network.openGraph configuration).dist first network.source =
      (network.openGraph configuration).dist network.source first from SimpleGraph.dist_comm] at triangle
    exact triangle.trans (by
      have first_bound := source_distance_le_terminalComponentRadius network configuration first
      have last_bound := source_distance_le_terminalComponentRadius network configuration last
      omega)
  · have triangle := reachable.symm.dist_triangle_left last
    rw [show (network.openGraph configuration).dist first network.target =
      (network.openGraph configuration).dist network.target first from SimpleGraph.dist_comm] at triangle
    exact triangle.trans (by
      have first_bound := target_distance_le_terminalComponentRadius network configuration first
      have last_bound := target_distance_le_terminalComponentRadius network configuration last
      omega)

theorem normalized_selected_component_distance_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (source_selected target_selected : Bool)
    (first last : Fin (rule.generation depth).vertices)
    (selected : (rule.generation depth).network.selectedActive source_selected target_selected
      (markedGenerationConfiguration rule marks depth address opened) first = true)
    (same_component : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth address opened)).Reachable first last)
    (scale mesh : ℝ) (scale_positive : 0 < scale)
    (radius_bound : (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
      scale ^ (depth + 1 + address.length) ≤ mesh) :
    (((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth address opened)).dist
      first last : ℝ) / scale ^ (depth + 1 + address.length) ≤ 2 * mesh := by
  have distance_bound := selected_component_distance_le_twice_radius (rule.generation depth).network
    (markedGenerationConfiguration rule marks depth address opened) source_selected target_selected first last selected same_component
  have cast_bound : (((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth address opened)).dist first last : ℝ) ≤
      2 * (markedTerminalComponentRadius rule marks depth address opened : ℝ) := by exact_mod_cast distance_bound
  calc
    _ ≤ (2 * (markedTerminalComponentRadius rule marks depth address opened : ℝ)) /
        scale ^ (depth + 1 + address.length) := div_le_div_of_nonneg_right cast_bound (pow_pos scale_positive _).le
    _ = 2 * ((markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length)) := mul_div_assoc _ _ _
    _ ≤ 2 * mesh := mul_le_mul_of_nonneg_left radius_bound (by norm_num)

end IGSIII.Geometry
