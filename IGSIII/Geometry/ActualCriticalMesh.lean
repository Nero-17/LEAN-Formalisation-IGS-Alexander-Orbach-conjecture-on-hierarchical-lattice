import IGSIII.Chemical.TerminalEnvelope
import IGSIII.Geometry.ActualSkeletonNets

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped ENNReal Topology

/-- On the actual common innovation space, every geometric mesh rate strictly
above the reciprocal chemical growth is valid for all descendant components.
The required high moment is proved by the endogenous field theorem. -/
theorem exists_actual_critical_uniform_component_mesh (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ growth : ℝ,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∀ eta : ℝ, 0 < eta → eta < 1 → 1 < growth * eta →
        ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
          ∃ start : ℕ, ∀ address opened depth, start ≤ address.length →
            (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
              growth ^ (depth + 1 + address.length) ≤
                ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ address.length := by
  obtain ⟨constant, growth, _, _, growth_lower, growth_upper, _, moments, terminal_bound⟩ :=
    exists_actual_chemical_terminal_envelope rule classicalRule p positive below_one fixed_point
  refine ⟨growth, growth_lower, growth_upper, ?_⟩
  intro eta eta_positive eta_lt_one product_gt_one
  have growth_gt_one : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growth_lower
  have large_power := (tendsto_pow_atTop_atTop_of_one_lt product_gt_one).eventually (eventually_gt_atTop (rule.edges : ℝ))
  obtain ⟨power, power_positive, moment_growth⟩ := ((eventually_gt_atTop (0 : ℕ)).and large_power).exists
  obtain ⟨bound, bound_finite, moment_bounds⟩ := moments (power : ℝ≥0∞) (by exact_mod_cast power_positive) (by simp)
  exact ae_uniform_actual_component_mesh rule (independentInnovationLaw rule p positive below_one fixed_point)
    growth eta growth_gt_one eta_positive eta_lt_one product_gt_one.le power power_positive moment_growth
    (chemicalTerminalEnvelope rule p positive below_one fixed_point growth)
    (fun address opened => (moment_bounds address opened).1.aestronglyMeasurable)
    bound bound_finite (fun address opened => (moment_bounds address opened).2) terminal_bound

/-- The entire actual critical retained cluster, including all dangling
branches and both noncrossing sides, has exponentially fine actual birth nets.
This theorem has no assumed terminal moment or mesh certificate. -/
theorem exists_actual_critical_cluster_skeleton_nets (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ growth : ℝ,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∀ eta : ℝ, 0 < eta → eta < 1 → 1 < growth * eta →
        ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
          ∃ start : ℕ, ∀ age depth opened source_side (vertex : Fin (rule.generation depth).vertices),
            start ≤ age + 1 →
            ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] opened)).Reachable
              (plantedVertex (rule.generation depth).network source_side) vertex →
            ∃ anchor ∈ finiteSkeletonVertices rule depth age,
              ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] opened)).Reachable
                (plantedVertex (rule.generation depth).network source_side) anchor ∧
              (((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] opened)).dist anchor vertex : ℝ) /
                growth ^ (depth + 1) ≤ ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (age + 1) := by
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
  intro age depth opened source_side vertex beyond reachable
  have coefficient_nonnegative : 0 ≤ (rule.edges + 1 : ℝ) / (1 - eta) :=
    div_nonneg (by positivity) (sub_pos.mpr eta_lt_one).le
  have actual_net := finite_skeleton_is_net_of_component_radius_bounds rule marks growth eta
    ((rule.edges + 1 : ℝ) / (1 - eta)) start growth_positive eta_positive.le coefficient_nonnegative
    radius_bounds depth age [] opened source_side vertex (by simpa using beyond) reachable
  simpa only [List.length_nil, Nat.add_zero, Nat.zero_add] using actual_net

end IGSIII.Geometry
