import IGSIII34.Forms.ActualEnergyHilbert

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)

include anchor in
/-- The actual full resistance energy vanishes exactly on constants,
including every point of its completion. -/
theorem actual_energy_zero_iff_completed_constant_completion20261011
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :
    limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val = 0 ↔
    ∃ constant : ℝ,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential =
        ContinuousMap.const _ constant := by
  constructor
  · intro zero
    refine ⟨actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential anchor, ?_⟩
    ext point
    have bound := actualEnergyExtension_resistance rule p positive belowOne fixedPoint growth value growthPositive marks potential point anchor
    rw [zero, mul_zero] at bound
    change actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point =
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential anchor
    nlinarith [sq_nonneg (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point -
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential anchor)]
  · rintro ⟨constant, equality⟩
    have values : potential.val = fun _ => constant := by
      funext vertex
      have coeValue := completionExtension_coe
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
        potential vertex
      have pointEquality := congrArg (fun function => function (UniformSpace.Completion.coe' vertex)) equality
      exact coeValue.symm.trans pointEquality
    rw [values]
    change (⨆ depth, finiteEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks depth)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks depth) (fun _ => constant)) = 0
    simp only [finiteEnergy_constant, ciSup_const]

end
end IGSIII34.Forms

#print axioms IGSIII34.Forms.actual_energy_zero_iff_completed_constant_completion20261011
