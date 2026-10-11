import IGSIII34.ResistanceLimit.ActualHarmonicDensity
import IGSIII34.ResistanceLimit.ActualTraceUniqueness

/-! The canonical actual form attains every finite trace minimum. This is
the existence companion to uniqueness among competing complete forms. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
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

theorem actual_finite_trace_minimum_attained (depth : ℕ)
    (boundary : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ) :
    ∃ potential : energyDomain
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)),
      (∀ vertex, potential.val (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) =
        boundary (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) depth vertex)) ∧
      limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) potential.val =
      traceEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) depth boundary := by
  refine ⟨⟨actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks depth boundary,
    actualHarmonicInterpolation_finite rule p positive belowOne fixedPoint growth value growthPositive marks depth boundary⟩,
    ?_, ?_⟩
  · intro vertex
    exact harmonicInterpolation_boundary rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 depth boundary vertex
  · exact (harmonicTowerFunction_limiting_energy rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 marks.property.1.2 depth _).trans
      (skeleton_traceEnergy_eq_source_energy rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 depth boundary).symm

end
end IGSIII34.ResistanceLimit
