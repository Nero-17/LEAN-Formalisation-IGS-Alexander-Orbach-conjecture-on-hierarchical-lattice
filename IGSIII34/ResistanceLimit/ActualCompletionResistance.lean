import IGSIII34.ResistanceLimit.CompletionVariationalResistance
import IGSIII34.ResistanceLimit.ActualResistanceAttainment

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

theorem actual_completion_variational_resistance_eq
    (first last : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) :
    completionVariationalResistance
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      first last = dist first last := by
  exact completionVariationalResistance_eq_dist
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_skeleton_resistance_attained rule p positive belowOne fixedPoint growth value growthPositive marks) first last

end
end IGSIII34.ResistanceLimit
