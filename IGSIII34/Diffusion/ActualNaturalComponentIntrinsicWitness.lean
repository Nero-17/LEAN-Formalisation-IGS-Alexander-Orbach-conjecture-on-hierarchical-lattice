import IGSIII34.Diffusion.ActualElectricalComponentInclusion
import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation MeasureTheory
open IGSIII.Chemical.Substitution

/-- The SAME actual natural physical field supplies the intrinsic component
compatibility event simultaneously at every address and either planted side. -/
theorem ae_actual_natural_component_electrical_typical
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ComponentElectricalTypical rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) marks := by
  have amplitudePositive := zero_lt_one.trans_le natural.amplitudeLower
  have valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < (natural.amplitude • natural.field) marks := by
    filter_upwards [natural.fieldPositive, Lp.coeFn_smul natural.amplitude natural.field] with marks fieldPositive scalar
    rw [scalar]
    exact mul_pos amplitudePositive fieldPositive
  have fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 natural.growth
      (natural.amplitude • natural.field) = natural.amplitude • natural.field := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 natural.growth
      natural.amplitude amplitudePositive.le, natural.fieldFixed]
  exact componentElectricalTypical_ae rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) valuePositive fixed

end
end IGSIII34.Diffusion
