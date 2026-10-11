import IGSIII34.ResistanceLimit.ActualHarmonic
import IGSIII34.ResistanceLimit.HarmonicDensity

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

def actualHarmonicInterpolation (initial : ℕ)
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ) :=
  harmonicInterpolation rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 initial potential

theorem actualHarmonicInterpolation_finite (initial : ℕ)
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ) :
    actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks initial potential ∈
      energyDomain
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) :=
  harmonicInterpolation_finite rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 marks.property.1.2 initial potential

theorem actual_harmonic_residual_energy_tendsto
    (potential : energyDomain
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) :
    Tendsto (fun initial => limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (fun point => potential.val point -
        actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks initial potential.val point))
      atTop (𝓝 0) :=
  harmonicInterpolation_residual_energy_tendsto rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 marks.property.1.2 potential

end
end IGSIII34.ResistanceLimit
