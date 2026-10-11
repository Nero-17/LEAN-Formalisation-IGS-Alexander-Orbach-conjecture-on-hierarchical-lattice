import IGSIII34.ResistanceLimit.ActualHarmonic
import IGSIII34.ResistanceLimit.HarmonicResistance

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

theorem actual_skeleton_resistance_attained :
    ∀ first last : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks),
      first ≠ last → ∃ potential : energyDomain
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)),
        potential.val first = 0 ∧ potential.val last = 1 ∧
        limitingEnergy
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
          potential.val = (dist first last)⁻¹ :=
  skeleton_resistance_attained rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 marks.property.1.2

end
end IGSIII34.ResistanceLimit
