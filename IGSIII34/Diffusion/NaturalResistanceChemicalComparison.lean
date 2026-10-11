import IGSIII34.Percolation.Continuation.NaturalResistanceExponents
import IGSIII34.Percolation.GenerationMean
import IGSIII.Chemical.ChemicalScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Probability
open IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall MeasureTheory

/-- Unit-edge electrical resistance is bounded by the genuine open graph
chemical distance, including noncrossing configurations. -/
theorem unitConfigurationResistance_le_chemical_distance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges) :
    unitConfigurationResistance network configuration ≤
      ((network.openGraph configuration).dist network.source network.target : ℝ) := by
  by_cases crossing : network.crosses configuration = true
  · have bound := (IGSIII34.Percolation.network network configuration).unitResistance_le_distance
      (connected_of_crosses network configuration crossing)
    rw [graph_eq_openGraph] at bound
    simpa only [unitConfigurationResistance, electricalCell, IGSIII34.Percolation.network] using bound
  · rw [unitConfigurationResistance, electricalCell_eq_zero_of_not_crosses _ _ crossing]
    exact Nat.cast_nonneg _

/-- Comparison before expectation, with the same original connected
configuration weights on the full graph. -/
theorem conditionalMeanResistance_le_conditionedDistanceMean {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (p : ℝ)
    (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1) :
    conditionalMeanResistance network p ≤ conditionedDistanceMean network p := by
  rw [← finiteMean_conditional_unitResistance]
  exact finiteMean_mono _ (network.conditionalCellWeight_nonneg nonnegative atMostOne true)
    (unitConfigurationResistance_le_chemical_distance network)

/-- The natural electrical multiplier is at most every chemical multiplier
with the actual Section 2 mean-growth bound. -/
theorem natural_electrical_growth_le_chemical_growth
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (chemicalGrowth : ℝ) (chemicalGrowthPositive : 0 < chemicalGrowth)
    (constant : ℝ) (meanUpper : ∀ depth, manuscriptDistanceMean rule p depth ≤ constant * chemicalGrowth ^ depth) :
    natural.growth ≤ chemicalGrowth := by
  obtain ⟨electricalConstant, electricalConstantPositive, growthBounds, _, _⟩ :=
    natural_physical_omega_witness_completion20261011 rule classicalRule p positive belowOne fixedPoint natural
  apply base_le_of_uniform_pow_comparison chemicalGrowthPositive
  intro depth
  have comparison : (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ manuscriptDistanceMean rule p depth := by
    cases depth with
    | zero => simp [electricalOrbitScale, manuscriptDistanceMean]
    | succ depth =>
      rw [electricalOrbitScale_succ_eq_generation_mean rule classicalRule p positive belowOne fixedPoint]
      exact conditionalMeanResistance_le_conditionedDistanceMean _ p positive.le belowOne.le
  exact (growthBounds depth).1.trans (comparison.trans (meanUpper depth))


/-- The Section 2 scalar construction supplies the chemical comparison
bound on the same critical model, without a new asymptotic premise. -/
theorem exists_actual_chemical_mean_growth_above_natural_resistance
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∃ constant chemicalGrowth : ℝ, 0 < constant ∧ 0 < chemicalGrowth ∧
      (∀ depth, chemicalGrowth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * chemicalGrowth ^ depth) ∧
      natural.growth ≤ chemicalGrowth := by
  obtain ⟨constant, chemicalGrowth, constantPositive, _, chemicalLower, _, meanBounds, rest⟩ :=
    exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  have chemicalPositive : 0 < chemicalGrowth :=
    lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale) chemicalLower
  exact ⟨constant, chemicalGrowth, constantPositive, chemicalPositive, meanBounds,
    natural_electrical_growth_le_chemical_growth rule classicalRule p positive belowOne fixedPoint natural
      chemicalGrowth chemicalPositive constant⁻¹ (fun depth => (meanBounds depth).2)⟩

end
end IGSIII34.Diffusion
