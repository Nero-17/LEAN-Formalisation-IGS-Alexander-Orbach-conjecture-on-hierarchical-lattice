import IGSIII34.ResistanceLimit.ActualComponentIntrinsicEnergyBridge
import IGSIII34.ResistanceLimit.ActualElectricalChemicalCellIdentification
import IGSIII34.ResistanceLimit.ActualElectricalChemicalZeroExtension
import IGSIII34.Diffusion.ActualNaturalComponentIntrinsicWitness
import IGSIII34.ResistanceLimit.CompletionLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution MeasureTheory

/-- All actual probabilistic inputs to component decomposition, intrinsic
restriction, closed-cell identification and zero extension hold on the SAME
original natural innovation event. No inverse metric or locality is assumed. -/
theorem ae_actual_natural_component_energy_event
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ComponentElectricalTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks ∧
      StationaryEnergyTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks ∧
      (∀ address, electricalCell rule.network (marks (address, true))
        (fun edge => electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) (address ++ [edge]) marks) =
          natural.growth * electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) address marks) := by
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
  filter_upwards [ae_actual_natural_component_electrical_typical rule p positive belowOne fixedPoint natural,
    stationaryEnergyTypical_ae rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne) valuePositive fixed,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint natural.growth (zero_lt_one.trans natural.aboveOne)
      (natural.amplitude • natural.field) valuePositive fixed] with marks component energy stationary
  exact ⟨component, energy, stationary⟩

end
end IGSIII34.ResistanceLimit
