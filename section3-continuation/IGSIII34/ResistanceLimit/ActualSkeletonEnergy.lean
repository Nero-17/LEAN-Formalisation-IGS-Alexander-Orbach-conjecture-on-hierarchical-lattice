import IGSIII34.ResistanceLimit.ActualStationaryCompletion
import IGSIII34.ResistanceLimit.StationarySourceGeneration
import IGSIII34.ResistanceLimit.SkeletonEnergy

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

/-- Actual innovations satisfy both metric and energy compatibility on this
proved full-measure event. The energy clause is independent of pair distances. -/
def StationaryEnergyTypical
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : Prop :=
  StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks ∧
  ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
    sourceComponentEnergy (network (rule.generation depth).network (stationaryConfiguration rule marks depth))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks depth)
      (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
    sourceComponentEnergy (network (rule.generation (depth + 1)).network (stationaryConfiguration rule marks (depth + 1)))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks (depth + 1)) potential

theorem stationaryEnergyTypical_ae
    (growthPositive : 0 < growth)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks := by
  filter_upwards [stationaryElectricalTypical_ae rule p positive belowOne fixedPoint growth value growthPositive
      valuePositive fixed,
    actual_stationary_generation_source_energy_le rule p positive belowOne fixedPoint growth growthPositive
      value valuePositive fixed] with marks electrical energy
  exact ⟨electrical, fun depth potential => energy depth [] true potential⟩

variable (growthPositive : 0 < growth)
variable (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

def energyTypicalElectricalMarks :
    {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks} :=
  ⟨marks.val, marks.property.1⟩

def ActualStationaryEnergySkeleton :=
  ElectricalSkeleton rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    marks.property.1.2.2

instance actualStationaryEnergySkeletonMetricSpace :
    MetricSpace (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  unfold ActualStationaryEnergySkeleton
  infer_instance

def actualEnergyEndpoint := skeletonEnergyEndpoint rule (stationaryConfiguration rule marks.val)
  (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
    (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
  (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
  (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
    (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) marks.property.1.2.2

def actualEnergyConductance := skeletonEnergyConductance rule (stationaryConfiguration rule marks.val)
  (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)

include growthPositive in
theorem actualEnergyConductance_nonnegative :
    ∀ depth edge, 0 ≤ actualEnergyConductance rule p positive belowOne fixedPoint growth value marks depth edge :=
  skeletonEnergyConductance_nonnegative rule (stationaryConfiguration rule marks.val)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))

theorem actual_traceEnergy_monotone
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ) :
    Monotone (fun depth => traceEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) depth potential) :=
  skeleton_traceEnergy_monotone rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    marks.property.1.2.2 marks.property.2 potential

theorem actual_finite_energy_resistance_bound
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (finite : potential ∈ energyDomain
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    ∀ first last, (potential first - potential last) ^ 2 ≤ dist first last *
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential :=
  skeleton_finite_energy_resistance_bound rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    marks.property.1.2.2 potential finite

end
end IGSIII34.ResistanceLimit
