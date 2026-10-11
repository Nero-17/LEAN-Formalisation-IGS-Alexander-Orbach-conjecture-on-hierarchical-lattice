import IGSIII4.SupersolutionConditionalBound
import IGSIII4.AcceptedSectionThree

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Chemical.Substitution IGSIII34.Percolation
open scoped NNReal Topology

theorem critical_supersolution_domination_positive_input (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) (valuePositive : ∀ marks, 0 < (value marks : ℝ))
    (integrable : Integrable (fun marks => (value marks : ℝ))
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseIntegrable : Integrable (fun marks => (value marks : ℝ)⁻¹)
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseMeanPositive : 0 < ∫ marks, (value marks : ℝ)⁻¹
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule (fun marks => (value marks : ℝ)) marks ≤ accepted.growth * (value marks : ℝ)) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      accepted.field marks ≤
        (∫ other, (value other : ℝ)⁻¹ ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
          (value marks : ℝ) := by
  have growthPositive : 0 < accepted.growth := zero_lt_one.trans accepted.growthAboveOne
  have conditionalComparison (depth : ℕ) :
      ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
        (condExp (innovationFiltration rule (depth + 1))
          (independentInnovationLaw rule probability positive belowOne fixedPoint) accepted.field) marks ≤
        (∫ other, (value other : ℝ)⁻¹ ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
          (condExp (innovationFiltration rule (depth + 1))
            (independentInnovationLaw rule probability positive belowOne fixedPoint)
            (fun marks => (value marks : ℝ))) marks := by
    filter_upwards [accepted.conditionalLower depth,
      supersolution_conditional_bound rule probability positive belowOne fixedPoint value measurable valuePositive
        integrable inverseIntegrable inverseMeanPositive growthPositive supersolution depth] with marks lower upper
    apply (mul_le_mul_iff_of_pos_left (pow_pos growthPositive (depth + 1))).mp
    exact lower.trans (by simpa only [mul_assoc] using upper)
  filter_upwards [ae_all_iff.mpr conditionalComparison,
    innovation_condExp_converges rule probability positive belowOne fixedPoint accepted.field
      accepted.fieldMeasurable accepted.fieldIntegrable,
    innovation_condExp_converges rule probability positive belowOne fixedPoint (fun marks => (value marks : ℝ))
      (measurable_coe_nnreal_real.comp measurable) integrable] with marks comparison fieldConverges valueConverges
  exact le_of_tendsto_of_tendsto
    (fieldConverges.comp (tendsto_add_atTop_nat 1))
    (tendsto_const_nhds.mul (valueConverges.comp (tendsto_add_atTop_nat 1)))
    (Eventually.of_forall comparison)

end
end IGSIII4
