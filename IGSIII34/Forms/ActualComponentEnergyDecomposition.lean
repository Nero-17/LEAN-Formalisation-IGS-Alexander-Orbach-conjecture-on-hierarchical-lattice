import IGSIII34.Forms.RetainedComponentLimits
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


def actualComponentPotentialStage (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) : ℝ :=
  potential (electricalSkeletonPoint rule (stationaryConfiguration rule marks.val) (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val) (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) marks.property.1.2.2 depth vertex)

theorem actualComponentPotentialStage_restriction (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential (depth + 1) (rule.generationOldVertex depth vertex) =
      actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential depth vertex := by
  unfold actualComponentPotentialStage
  rw [electricalSkeletonPoint_old]

/-- The energy contribution of the genuine retained closed component is
computed from its own selected descendant edges in global normalization. -/
def actualRetainedComponentEnergy (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (age : ℕ) (word : Fin age → (Fin rule.edges × Bool)) : ℝ :=
  ⨆ fine, retainedWordTraceEnergy rule marks.val marks.property.1.2.1 fine age
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (fine + age))
    (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential (fine + age)) word

theorem actual_form_component_energy_decomposition
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (finite : potential ∈ energyDomain (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks) (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)) (age : ℕ) :
    limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks) (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential =
      ∑ word : Fin age → (Fin rule.edges × Bool), actualRetainedComponentEnergy rule p positive belowOne fixedPoint growth value growthPositive marks potential age word := by
  have traceIdentity (depth : ℕ) := skeleton_traceEnergy_eq_source_energy rule (stationaryConfiguration rule marks.val) (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val) (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) marks.property.1.2.2 depth potential
  have sourceFinite : BddAbove (Set.range (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth)
      (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential depth))) := by
    obtain ⟨upper, upperBound⟩ := finite
    refine ⟨upper, ?_⟩
    rintro energy ⟨depth, rfl⟩
    exact (traceIdentity depth).symm.le.trans (upperBound (Set.mem_range_self depth))
  have decomposition := stationary_retained_component_energy_decomposition rule marks.val marks.property.1.2.1
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) growth
    growthPositive marks.property.1.1 stationary
    (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential)
    (actualComponentPotentialStage_restriction rule p positive belowOne fixedPoint growth value growthPositive marks potential) age sourceFinite
  change (⨆ depth, traceEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks) (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) depth potential) = _
  calc
    _ = ⨆ depth, sourceComponentEnergy
        (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth)
        (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive marks potential depth) := by
      congr 1
      funext depth
      exact traceIdentity depth
    _ = _ := decomposition

end
end IGSIII34.Forms
