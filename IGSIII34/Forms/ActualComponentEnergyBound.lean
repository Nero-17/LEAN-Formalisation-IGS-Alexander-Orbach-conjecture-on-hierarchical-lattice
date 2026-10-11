import IGSIII34.Forms.ActualComponentEnergyDecomposition
import IGSIII34.ResistanceLimit.ActualSkeletonEnergy

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory
open scoped BigOperators

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})


theorem actualRetainedComponent_trace_bddAbove
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (finite : potential ∈ energyDomain (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks) (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks))
    (age : ℕ) (word : Fin age → (Fin rule.edges × Bool)) :
    BddAbove (Set.range (fun fine => retainedWordTraceEnergy rule marks.val marks.property.1.2.1 fine age
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (fine + age))
      (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential (fine + age)) word)) := by
  classical
  obtain ⟨upper, upperBound⟩ := finite
  refine ⟨upper, ?_⟩
  rintro energy ⟨fine, rfl⟩
  have nonnegative (other : Fin age → (Fin rule.edges × Bool)) := retainedWordTraceEnergy_nonnegative
    rule marks.val marks.property.1.2.1 fine age
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (fine + age))
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks) (fine + age))
    (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential (fine + age)) other
  have bound := Finset.single_le_sum (fun other (_ : other ∈ Finset.univ) => nonnegative other) (Finset.mem_univ word)
  have partition := sourceComponentEnergy_eq_sum_retained_word_energy rule marks.val marks.property.1.2.1 fine age
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (fine + age))
    (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential (fine + age))
  rw [← partition] at bound
  have traceIdentity := skeleton_traceEnergy_eq_source_energy rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    marks.property.1.2.2 (fine + age) potential
  exact bound.trans (traceIdentity.symm.le.trans (upperBound (Set.mem_range_self (fine + age))))

end
end IGSIII34.Forms
