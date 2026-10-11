import IGSIII4.ConditionalHarmonic
import IGSIII4.TransferIteration

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII34.Percolation
open scoped NNReal

theorem supersolution_conditional_bound (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) (valuePositive : ∀ marks, 0 < (value marks : ℝ))
    (integrable : Integrable (fun marks => (value marks : ℝ))
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseIntegrable : Integrable (fun marks => (value marks : ℝ)⁻¹)
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseMeanPositive : 0 < ∫ marks, (value marks : ℝ)⁻¹
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    {factor : ℝ} (factorPositive : 0 < factor)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule (fun marks => (value marks : ℝ)) marks ≤ factor * (value marks : ℝ))
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true) ≤
      factor ^ (depth + 1) *
        (∫ other, (value other : ℝ)⁻¹
          ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
        (condExp (innovationFiltration rule (depth + 1))
          (independentInnovationLaw rule probability positive belowOne fixedPoint)
          (fun marks => (value marks : ℝ))) marks := by
  have conditionalComparison := condExp_mono (m := innovationFiltration rule (depth + 1))
    (electricalTransfer_iterate_integrable rule probability positive belowOne fixedPoint _
      (measurable_coe_nnreal_real.comp measurable) (fun marks => (value marks).coe_nonneg) integrable (depth + 1))
    (integrable.const_mul (factor ^ (depth + 1)))
    (supersolution_iterate_bound rule probability positive belowOne fixedPoint _
      (fun marks => (value marks).coe_nonneg) factorPositive.le supersolution (depth + 1))
  have conditionalScaling := condExp_smul (μ := independentInnovationLaw rule probability positive belowOne fixedPoint)
    (factor ^ (depth + 1)) (fun marks => (value marks : ℝ)) (innovationFiltration rule (depth + 1))
  change condExp (innovationFiltration rule (depth + 1))
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (fun marks => factor ^ (depth + 1) * (value marks : ℝ))
      =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
    (fun marks => factor ^ (depth + 1) *
      (condExp (innovationFiltration rule (depth + 1))
        (independentInnovationLaw rule probability positive belowOne fixedPoint)
        (fun marks => (value marks : ℝ))) marks) at conditionalScaling
  filter_upwards [electricalTransfer_condExp_iterate_lower_bound rule probability positive belowOne fixedPoint
    value measurable valuePositive integrable inverseIntegrable inverseMeanPositive depth,
    conditionalComparison, conditionalScaling] with marks lower comparison scaling
  rw [scaling] at comparison
  have bound := (div_le_iff₀ inverseMeanPositive).mp (lower.trans comparison)
  nlinarith only [bound]

end
end IGSIII4
