import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion20261011
import IGSIII34.Percolation.Continuation.ElectricalReciprocal
import IGSIII34.Resistance.IIDComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Probability
open IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory Filter
open scoped _root_.Topology ENNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p)
  (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)

/-- The full conditional reciprocal sandwich on the original generation graph,
for the SAME natural mean-one stationary electrical field. -/
theorem actual_natural_unit_graph_conditional_reciprocal_sandwich
    (classicalRule : rule.Classical) (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < (independentInnovationLaw rule p positive belowOne fixedPoint)[
        fun marks => (natural.field marks)⁻¹ |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
          (depth + 1)] marks ∧
      (independentInnovationLaw rule p positive belowOne fixedPoint)[⇑natural.field |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
          (depth + 1)] marks ≤
        growthScaledResistance rule natural.growth depth
          (markedGenerationConfiguration rule marks depth [] true) ∧
      growthScaledResistance rule natural.growth depth
          (markedGenerationConfiguration rule marks depth [] true) ≤
        (∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) /
          (independentInnovationLaw rule p positive belowOne fixedPoint)[
            fun marks => (natural.field marks)⁻¹ |
            coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
              (depth + 1)] marks ∧
      (∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) /
          (independentInnovationLaw rule p positive belowOne fixedPoint)[
            fun marks => (natural.field marks)⁻¹ |
            coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
              (depth + 1)] marks ≤
        (∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) *
          (independentInnovationLaw rule p positive belowOne fixedPoint)[⇑natural.field |
            coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
              (depth + 1)] marks := by
  have inverseIntegrable : Integrable (fun marks => (natural.field marks)⁻¹)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    simpa only [Real.rpow_neg_one] using natural.fieldMoments (-1)
  have bounds := electricalOrbit_conditional_fixed_reciprocal_sandwich
    rule p positive belowOne fixedPoint natural.growth (zero_lt_one.trans natural.aboveOne)
    natural.field natural.fieldPositive natural.fieldFixed natural.fieldMeanOne inverseIntegrable
    (∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint)
    (inverse_mean_positive (independentInnovationLaw rule p positive belowOne fixedPoint)
      natural.field natural.fieldPositive inverseIntegrable) rfl depth
  rw [electricalOrbitLp_tail_eq_actual rule
    classicalRule p positive belowOne fixedPoint natural.growth
    (zero_lt_one.trans natural.aboveOne).le depth] at bounds
  filter_upwards [bounds, markedObservableLp_ae rule p positive belowOne fixedPoint depth [] true
    (growthScaledResistance rule natural.growth depth)] with marks bound equality
  dsimp only at bound
  rwa [equality] at bound

/-- Literal L² compactness of the original unit-edge normalized graph family;
the growth bounds are proved from the SAME natural witness. -/
theorem actual_natural_unit_graph_L2_compact_closure
    (classicalRule : rule.Classical) (address : List (Fin rule.edges)) :
    IsCompact (closure (markedGrowthScaledResistanceFamily
      rule p positive belowOne fixedPoint address natural.growth)) := by
  obtain ⟨constant, _, growthBounds, _, _⟩ :=
    natural_physical_omega_witness_completion20261011 rule classicalRule p positive belowOne fixedPoint natural
  exact markedGrowthScaledResistanceFamily_compact_closure rule classicalRule p positive belowOne fixedPoint
    address constant natural.growth (zero_lt_one.trans natural.aboveOne) growthBounds

/-- Uniform moments of every real order, including negative orders, for the
original electrical iteration, with no externally assumed moment bound. -/
theorem actual_natural_electrical_iteration_uniform_real_moment
    (classicalRule : rule.Classical) (exponent : ℝ) :
    ∃ bound : ℝ, ∀ depth,
      Integrable (fun marks => (natural.growth⁻¹ ^ depth * electricalIteration rule marks depth []) ^ exponent)
        (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (∫ marks, (natural.growth⁻¹ ^ depth * electricalIteration rule marks depth []) ^ exponent
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨constant, constantPositive, growthBounds, _, _⟩ :=
    natural_physical_omega_witness_completion20261011 rule classicalRule p positive belowOne fixedPoint natural
  obtain ⟨bound, bounds⟩ := electricalOrbit_uniform_integrable_real_moment rule classicalRule
    p positive belowOne fixedPoint constant natural.growth constantPositive
    (zero_lt_one.trans natural.aboveOne) growthBounds exponent
  refine ⟨bound, fun depth => ?_⟩
  have equality := (electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint
    natural.growth (zero_lt_one.trans natural.aboveOne).le depth).mono
    (fun marks equality => congrArg (fun value : ℝ => value ^ exponent) equality)
  exact ⟨(bounds depth).1.congr equality, (integral_congr_ae equality).symm.trans_le (bounds depth).2⟩

/-- All positive moments of the full original depth supremum, on every actual
address, for the SAME natural multiplier. -/
theorem actual_natural_electrical_iteration_supremum_moment
    (address : List (Fin rule.edges)) (exponent : ℝ) (exponentPositive : 0 < exponent) :
    (∫⁻ marks, (⨆ depth : ℕ,
      ENNReal.ofReal (natural.growth⁻¹ ^ depth * electricalIteration rule marks depth address)) ^ exponent
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞ :=
  natural.supremumMoments address exponent exponentPositive

end
end IGSIII34.Diffusion
