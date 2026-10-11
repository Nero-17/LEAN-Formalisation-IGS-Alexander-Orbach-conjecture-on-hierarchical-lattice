import IGSIII34.ResistanceLimit.CompletionResistanceAttainment
import IGSIII34.ResistanceLimit.ActualResistanceAttainment

set_option autoImplicit false
set_option maxHeartbeats 1800000
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

theorem actual_completion_resistance_attained
    (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (first last : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))
    (distinct : first ≠ last) :
    ∃ potential : energyDomain
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)),
      limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        potential.val = dist first last ∧
      completionExtension
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) potential first -
      completionExtension
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) potential last =
        dist first last := by
  exact completion_resistance_attained
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    anchor (actual_skeleton_resistance_attained rule p positive belowOne fixedPoint growth value growthPositive marks)
    first last distinct

end
end IGSIII34.ResistanceLimit
