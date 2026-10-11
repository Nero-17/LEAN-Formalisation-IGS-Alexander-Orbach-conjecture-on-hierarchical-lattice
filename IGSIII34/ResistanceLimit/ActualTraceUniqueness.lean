import IGSIII34.ResistanceLimit.SkeletonTraceUniqueness
import IGSIII34.ResistanceLimit.ActualSkeletonEnergy

/-! The actual innovation-driven resistance form is determined by its finite
retained traces among complete anchored function Hilbert spaces. -/
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
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

def actualTraceVertex (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks :=
  electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) marks.property.1.2.2 depth vertex

theorem actual_form_unique_from_finite_traces
    {Energy : Type*} [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (evaluation : Energy →ₗ[ℝ]
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ))
    (injective : Function.Injective evaluation)
    (continuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (lower : ∀ boundary depth potential,
      (∀ vertex, evaluation potential (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex) =
        boundary (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)) →
      traceEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) depth boundary +
        boundary anchor ^ 2 ≤ ‖potential‖ ^ 2)
    (attained : ∀ boundary depth, ∃ potential,
      (∀ vertex, evaluation potential (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex) =
        boundary (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)) ∧
      ‖potential‖ ^ 2 = traceEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) depth boundary + boundary anchor ^ 2) :
    Set.range evaluation = {boundary | boundary ∈ energyDomain
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)} ∧
      ∀ potential, ‖potential‖ ^ 2 - evaluation potential anchor ^ 2 =
        limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) (evaluation potential) := by
  exact skeleton_form_unique_from_finite_traces rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) marks.property.1.2.2
    marks.property.2 anchor evaluation injective continuous lower attained

end
end IGSIII34.ResistanceLimit
