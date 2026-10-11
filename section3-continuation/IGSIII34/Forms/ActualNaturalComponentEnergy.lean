import IGSIII34.Forms.ActualComponentEnergyDecomposition
import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion20261011
import IGSIII34.ResistanceLimit.CompletionLocality

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory
open scoped BigOperators

theorem ae_actual_form_component_energy_decomposition
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ typical : StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks,
      ∀ potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ → ℝ,
      potential ∈ energyDomain (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩) (actualEnergyConductance rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩) (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩) →
      ∀ age, limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩) (actualEnergyConductance rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩) potential =
        ∑ word : Fin age → (Fin rule.edges × Bool), actualRetainedComponentEnergy rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ potential age word := by
  filter_upwards [electricalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive
    value valuePositive fixed] with marks stationary
  intro typical potential finite age
  exact actual_form_component_energy_decomposition rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ stationary potential finite age

/-- The actual natural witness discharges every probabilistic input to
component energy decomposition on the same original innovation event. -/
theorem ae_actual_natural_form_component_energy_decomposition
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ typical : StationaryEnergyTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks,
      ∀ potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ → ℝ,
      potential ∈ energyDomain (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) →
      ∀ age, limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) potential =
        ∑ word : Fin age → (Fin rule.edges × Bool), actualRetainedComponentEnergy rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ potential age word := by
  have amplitudePositive := zero_lt_one.trans_le natural.amplitudeLower
  have scaledPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < (natural.amplitude • natural.field) marks := by
    filter_upwards [natural.fieldPositive, Lp.coeFn_smul natural.amplitude natural.field] with marks positiveField equal
    rw [equal]
    exact mul_pos amplitudePositive positiveField
  have scaledFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 natural.growth
      (natural.amplitude • natural.field) = natural.amplitude • natural.field := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 natural.growth
      natural.amplitude amplitudePositive.le, natural.fieldFixed]
  exact ae_actual_form_component_energy_decomposition rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) scaledPositive scaledFixed

end
end IGSIII34.Forms
