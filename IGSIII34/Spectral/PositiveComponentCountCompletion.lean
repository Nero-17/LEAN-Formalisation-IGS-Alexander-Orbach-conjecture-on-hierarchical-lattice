import IGSIII34.Spectral.ActualLiveComponentCountCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Spectral
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

/-- Zero mass of inactive components transfers the proved live count to the
number of positive atoms of the actual boundary partition. -/
theorem positive_component_weight_count_le_live_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (inactiveZero : ∀ address, retainedComponentState rule marks address = .inactive → weight address = 0)
    (depth : ℕ) :
    (Finset.univ.filter fun word : Fin depth → (Fin rule.edges × Bool) =>
      0 < weight (List.ofFn word)).card ≤ actualLiveComponentCountCompletion rule marks depth := by
  classical
  apply Finset.card_le_card
  intro word member
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have positive := (Finset.mem_filter.mp member).2
  intro inactive
  rw [inactiveZero _ inactive] at positive
  exact lt_irrefl _ positive

theorem actual_positive_component_weight_Perron_count_bound_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ coefficient : ℝ, 0 < coefficient ∧
        ∀ weight : List (Fin rule.edges × Bool) → ℝ,
          (∀ address, retainedComponentState rule marks address = .inactive → weight address = 0) →
          ∀ depth : ℕ,
            ((Finset.univ.filter fun word : Fin depth → (Fin rule.edges × Bool) =>
              0 < weight (List.ofFn word)).card : ℝ) ≤
                coefficient * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth := by
  filter_upwards [actual_live_component_count_Perron_bound_completion rule classicalRule
    p positive belowOne fixedPoint] with marks population
  obtain ⟨coefficient, coefficientPositive, bound⟩ := population
  refine ⟨coefficient, coefficientPositive, ?_⟩
  intro weight inactiveZero depth
  exact (Nat.cast_le.mpr (positive_component_weight_count_le_live_completion
    rule marks weight inactiveZero depth)).trans (bound depth)

end
end IGSIII34.Spectral
