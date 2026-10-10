import IGSIII.Geometry.ComponentDiameterSupremumMoments

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Appendix full-mesh, fully instantiated on the actual model. The first
assertion takes the supremum over all remaining depths before the moment;
the second is uniform simultaneously over all descendants and depths. -/
theorem exists_actual_critical_full_component_mesh
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      (∀ order : ℝ≥0∞, order ≠ ∞ → ∀ address opened sourceSide,
        MemLp (markedComponentDiameterSupremum rule growth address opened sourceSide) order
          (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address opened sourceSide depth,
        (markedRetainedComponentDiameter rule depth address opened sourceSide marks : ℝ) / growth ^ (depth + 1) ≤
          markedComponentDiameterSupremum rule growth address opened sourceSide marks) ∧
      ∀ eta : ℝ, 0 < eta → eta < 1 → 1 < growth * eta →
        ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
          ∃ start : ℕ, ∀ address opened depth, start ≤ address.length →
            (markedRetainedComponentDiameter rule depth address opened true marks : ℝ) /
              growth ^ (depth + 1 + address.length) ≤
                (2 * ((rule.edges + 1 : ℝ) / (1 - eta))) * eta ^ address.length ∧
            (markedRetainedComponentDiameter rule depth address opened false marks : ℝ) /
              growth ^ (depth + 1 + address.length) ≤
                (2 * ((rule.edges + 1 : ℝ) / (1 - eta))) * eta ^ address.length := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds, _, _⟩ :=
    exists_actual_chemical_terminal_envelope rule classicalRule p positive belowOne fixedPoint
  have growthPositive : 0 < growth :=
    (show (0 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale).trans_le growthLower
  obtain ⟨diameterMoments, supremumBounds⟩ := actual_critical_component_diameter_supremum_moments_of_mean_bounds
    rule classicalRule p positive belowOne fixedPoint constant growth growthPositive meanBounds
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    diameterMoments, supremumBounds, ?_⟩
  intro eta etaPositive etaBelowOne productGreaterThanOne
  filter_upwards [actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint
    constant growth growthPositive meanBounds eta etaPositive etaBelowOne productGreaterThanOne] with marks bounds
  obtain ⟨start, radiusBounds⟩ := bounds
  refine ⟨start, ?_⟩
  intro address opened depth beyond
  have sideBound (sourceSide : Bool) :
      (markedRetainedComponentDiameter rule depth address opened sourceSide marks : ℝ) /
        growth ^ (depth + 1 + address.length) ≤
          (2 * ((rule.edges + 1 : ℝ) / (1 - eta))) * eta ^ address.length := by
    have bound := terminalRetainedComponentDiameter_le_twice_radius (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth address opened) sourceSide
    have castBound : (markedRetainedComponentDiameter rule depth address opened sourceSide marks : ℝ) ≤
        2 * (markedTerminalComponentRadius rule marks depth address opened : ℝ) := by exact_mod_cast bound
    calc
      _ ≤ (2 * (markedTerminalComponentRadius rule marks depth address opened : ℝ)) /
          growth ^ (depth + 1 + address.length) :=
            div_le_div_of_nonneg_right castBound (pow_pos growthPositive _).le
      _ = 2 * ((markedTerminalComponentRadius rule marks depth address opened : ℝ) /
          growth ^ (depth + 1 + address.length)) := by ring
      _ ≤ 2 * (((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ address.length) :=
        mul_le_mul_of_nonneg_left (radiusBounds address opened depth beyond) (by norm_num)
      _ = _ := by ring
  exact ⟨sideBound true, sideBound false⟩

end
end IGSIII.Geometry
