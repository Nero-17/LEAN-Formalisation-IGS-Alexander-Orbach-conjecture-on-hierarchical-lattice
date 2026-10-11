import IGSIII34.Spectral.Collars.PointMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open IGSIII34.Percolation IGSIII34.ResistanceLimit MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

/-- The genuine persistent retained vertex skeleton is countable: it is
the direct limit of the finite retained vertex sets. -/
theorem actual_stationary_energy_skeleton_countable :
    Countable (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  unfold ActualStationaryEnergySkeleton ElectricalSkeleton
  infer_instance

theorem actual_stationary_retained_skeleton_countable :
    (Set.range (UniformSpace.Completion.coe' (α :=
      ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))).Countable := by
  letI := actual_stationary_energy_skeleton_countable rule p positive belowOne fixedPoint growth value growthPositive marks
  exact Set.countable_range _

/-- Applied to `actual_physical_mass_null_singletons`, this is precisely
the retained-skeleton zero-mass assertion in Appendix B. -/
theorem actual_stationary_retained_skeleton_zero_mass
    [MeasurableSpace (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
    (measure : Measure (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    [NullSingletonClass measure] :
    measure (Set.range (UniformSpace.Completion.coe' (α :=
      ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))) = 0 :=
  (actual_stationary_retained_skeleton_countable rule p positive belowOne fixedPoint growth value growthPositive marks).measure_zero measure

end
end IGSIII34.Spectral
