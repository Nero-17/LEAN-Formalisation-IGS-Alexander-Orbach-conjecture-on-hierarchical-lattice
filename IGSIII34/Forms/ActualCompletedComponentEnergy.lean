import IGSIII34.Forms.ActualNaturalComponentEnergy

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit MeasureTheory
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

/-- The natural completed resistance form, rather than merely its finite
skeleton, has the exact finite retained-component energy decomposition. -/
theorem ae_actual_natural_completed_component_energy_decomposition
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ typical : StationaryEnergyTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks,
      ∀ potential : energyDomain (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩),
      ∀ age,
      limitingEnergy (completionEnergyEndpoint (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩)) (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
        (completionExtension (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) potential) =
        ∑ word : Fin age → (Fin rule.edges × Bool), actualRetainedComponentEnergy rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ potential.val age word := by
  filter_upwards [ae_actual_natural_form_component_energy_decomposition rule p positive belowOne fixedPoint natural]
    with marks decomposition
  intro typical potential age
  rw [completionExtension_limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩) (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩)]
  exact decomposition typical potential.val potential.property age

end
end IGSIII34.Forms
