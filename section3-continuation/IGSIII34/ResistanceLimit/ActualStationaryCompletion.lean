import IGSIII34.ResistanceLimit.ElectricalSkeleton
import IGSIII34.ResistanceLimit.StationaryGeneration

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

def stationaryConfiguration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) : Configuration (rule.generation depth).edges :=
  markedGenerationConfiguration rule marks depth [] true

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

def stationaryResistance
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (edge : {edge : Fin (rule.generation depth).edges // stationaryConfiguration rule marks depth edge = true}) : ℝ :=
  stationaryGenerationResistance rule
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks)
    growth depth [] edge.val

/-- This event is proved to have full measure below. Its compatibility clause
is the proved actual stationary generation identity, not an external input. -/
def StationaryElectricalTypical
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : Prop :=
  (∀ address, 0 < electricalField rule p positive belowOne fixedPoint value address marks) ∧
  (∀ address opened, rule.network.crosses (marks (address, opened)) = opened) ∧
  ∀ depth (first last : Fin (rule.generation depth).vertices),
    ((rule.generation depth).network.openGraph (stationaryConfiguration rule marks depth)).Reachable first last →
    pairResistance (network (rule.generation (depth + 1)).network (stationaryConfiguration rule marks (depth + 1)))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks (depth + 1))
      (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (stationaryConfiguration rule marks depth))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks depth) first last

theorem stationaryElectricalTypical_ae
    (growthPositive : 0 < growth)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks := by
  filter_upwards [electricalField_positive rule p positive belowOne fixedPoint value valuePositive,
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
    actual_stationary_generation_pair_compatible rule p positive belowOne fixedPoint growth growthPositive
      value valuePositive fixed] with marks fieldPositive crossing compatibility
  exact ⟨fieldPositive, crossing, fun depth first last reachable => compatibility depth [] true first last reachable⟩

variable (growthPositive : 0 < growth)
variable (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})

theorem typicalStationaryCoherent :
    configurationSequenceCoherent rule (stationaryConfiguration rule marks.val) :=
  fun depth => markedGenerationConfiguration_coarsens rule marks.val marks.property.2.1 depth [] true

include growthPositive in
theorem typicalStationaryResistance_positive :
    ∀ depth edge, 0 < stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth edge := by
  intro depth edge
  exact mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (marks.property.1 _)

def ActualStationaryElectricalSpace :=
  ElectricalSpace rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    marks.property.2.2

instance actualStationaryElectricalSpaceMetricSpace :
    MetricSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  unfold ActualStationaryElectricalSpace
  infer_instance

instance actualStationaryElectricalSpaceCompleteSpace :
    CompleteSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  unfold ActualStationaryElectricalSpace
  infer_instance

def actualStationaryElectricalVertex (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks :=
  electricalVertex rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    marks.property.2.2 depth vertex

theorem actualStationaryElectricalVertex_distance (depth : ℕ)
    (first last : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth first)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth last) =
      pairResistance (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth) first.val last.val :=
  electricalVertex_distance rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    marks.property.2.2 depth first last

theorem actualStationaryElectricalVertex_dense :
    Dense (⋃ depth, Set.range
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth)) :=
  electricalVertex_dense rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    marks.property.2.2

end
end IGSIII34.ResistanceLimit
