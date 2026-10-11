import IGSIII34.Forms.ActualComponentEnergyDecomposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

/-- Empty words contribute zero, so the exact all-word partition contains
only the energies of genuine retained physical components. -/
theorem actualRetainedComponentEnergy_inactive
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (age : ℕ) (word : Fin age → Fin rule.edges × Bool)
    (inactive : retainedComponentState rule marks.val (List.ofFn word) = .inactive) :
    actualRetainedComponentEnergy rule p positive belowOne fixedPoint growth value growthPositive marks potential age word = 0 := by
  have traceZero (fine : ℕ) : retainedWordTraceEnergy rule marks.val marks.property.1.2.1 fine age
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (fine + age))
      (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential (fine + age)) word = 0 := by
    unfold stationaryResistance
    erw [retainedWordTraceEnergy_stationary_scaling]
    simp only [selectedComponentTraceEnergy, if_pos inactive, mul_zero]
  unfold actualRetainedComponentEnergy
  simp only [traceZero, ciSup_const]

end
end IGSIII34.ResistanceLimit
