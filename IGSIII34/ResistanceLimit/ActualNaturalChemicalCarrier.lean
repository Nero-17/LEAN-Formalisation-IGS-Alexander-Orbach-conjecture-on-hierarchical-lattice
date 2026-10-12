import IGSIII34.ResistanceLimit.ActualChemicalCarrierIdentification
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

/-- The physical endpoint of every constructed natural-resistance witness
identifies its electrical completion with the actual chemical carrier and
constructs the common isometric chemical realization. No chemical lengths,
mesh, homeomorphism, or ambient realization is assumed. -/
theorem actual_natural_chemical_carrier_identification
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ActualChemicalCarrierIdentification rule classicalRule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  exact actual_chemical_carrier_identification_fixed_cluster rule classicalRule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
    constant constantPositive natural.aboveOne growthBounds fixed membership

theorem exists_actual_natural_chemical_carrier_identification
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint,
      ActualChemicalCarrierIdentification rule classicalRule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) := by
  obtain ⟨natural⟩ := exists_natural_resistance_completion rule classicalRule p positive belowOne fixedPoint
  exact ⟨natural, actual_natural_chemical_carrier_identification rule classicalRule p positive belowOne fixedPoint natural⟩

end
end IGSIII34.ResistanceLimit
