import IGSIII34.Forms.ActualComponentEnergyDecomposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

/-- Generation zero has just the whole retained root component, whose
energy is exactly the full form energy. This closes the age-zero case
without interpreting a positive-generation socket as the root. -/
theorem actualRetainedComponentEnergy_root
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ) :
    actualRetainedComponentEnergy rule p positive belowOne fixedPoint growth value growthPositive marks potential 0
      (fun index => Fin.elim0 index) =
    limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential := by
  unfold actualRetainedComponentEnergy limitingEnergy
  congr 1
  funext depth
  have partition := sourceComponentEnergy_eq_sum_retained_word_energy rule marks.val marks.property.1.2.1 depth 0
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (depth + 0))
    (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential (depth + 0))
  have traceIdentity := skeleton_traceEnergy_eq_source_energy rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) marks.property.1.2.2 depth potential
  erw [traceIdentity]
  change retainedWordTraceEnergy rule marks.val marks.property.1.2.1 depth 0
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth)
      (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential depth)
      (fun index => Fin.elim0 index) =
    sourceComponentEnergy (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth)
      (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential depth)
  have wordIdentity : (default : Fin 0 → Fin rule.edges × Bool) = (fun index => Fin.elim0 index) := by
    funext index
    exact Fin.elim0 index
  simpa only [Nat.add_zero, Fintype.sum_unique, wordIdentity, stationaryConfiguration] using partition.symm

end
end IGSIII34.ResistanceLimit
