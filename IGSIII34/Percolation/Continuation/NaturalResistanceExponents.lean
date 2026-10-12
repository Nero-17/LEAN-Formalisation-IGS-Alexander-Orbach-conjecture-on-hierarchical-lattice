import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion
import IGSIII34.Percolation.ResistanceTheorem

/-! All four logarithmic exponents belong to the same natural multiplier
used in the physical amplitudes, limiting form and diffusion clocks. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter IGSIII34.Probability
open IGSIII.Chemical.Substitution
open scoped _root_.Topology

theorem natural_resistance_exponents
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    deriv rule.network.reliability p ≤ natural.growth ∧
      natural.growth ≤ (∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _)) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address : List (Fin rule.edges),
          Tendsto (fun depth : ℕ => Real.log (electricalIteration rule marks depth address) / depth)
            atTop (𝓝 (Real.log natural.growth))) ∧
      (∀ address : List (Fin rule.edges),
        Tendsto (fun depth : ℕ => Real.log (∫ marks, electricalIteration rule marks depth address
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) / depth)
          atTop (𝓝 (Real.log natural.growth))) ∧
      (∀ address : List (Fin rule.edges),
        Tendsto (fun depth : ℕ => (∫ marks, Real.log (electricalIteration rule marks depth address)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) / depth)
          atTop (𝓝 (Real.log natural.growth))) ∧
      ∀ (address : List (Fin rule.edges)) (exponent : ℝ),
        Tendsto (fun depth : ℕ => Real.log (∫ marks, (electricalIteration rule marks depth address) ^ exponent
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) / depth)
          atTop (𝓝 (exponent * Real.log natural.growth)) := by
  obtain ⟨growth, aboveOne, lower, upper, almostSure, meanLimit, meanLogLimit, momentLimit⟩ :=
    exists_actual_resistance_exponent rule classicalRule p positive belowOne fixedPoint pathLength distanceBound
  obtain ⟨constant, _, growthBounds, _, _⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  have constantBound : 1 ≤ constant⁻¹ := by
    simpa only [pow_zero, mul_one] using (growthBounds 0).1.trans (growthBounds 0).2
  have naturalMeanLimit := tendsto_log_div_nat_of_growth_bounds
    (fun depth => (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ))
    natural.growth constant⁻¹ (zero_lt_one.trans natural.aboveOne) constantBound growthBounds
  simp only [electricalOrbitScale_eq_actual_mean rule classicalRule p positive belowOne fixedPoint] at naturalMeanLimit
  have growthEquality : growth = natural.growth :=
    Real.log_injOn_pos (zero_lt_one.trans aboveOne) (zero_lt_one.trans natural.aboveOne)
      (tendsto_nhds_unique (meanLimit []) naturalMeanLimit)
  subst growth
  exact ⟨lower, upper, almostSure, meanLimit, meanLogLimit, momentLimit⟩

end
end IGSIII34.Percolation
