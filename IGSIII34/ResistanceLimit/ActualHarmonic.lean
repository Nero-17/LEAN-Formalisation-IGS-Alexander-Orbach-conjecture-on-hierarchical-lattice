import IGSIII34.ResistanceLimit.ActualSkeletonEnergy
import IGSIII34.ResistanceLimit.StationaryHarmonicGeneration
import IGSIII34.ResistanceLimit.HarmonicTower

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

def StationaryHarmonicTypical
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : Prop :=
  StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks ∧
  ∀ depth (boundary : Fin (rule.generation depth).vertices → ℝ),
    ∃ potential : Fin (rule.generation (depth + 1)).vertices → ℝ,
      (∀ vertex, ((rule.generation depth).network.openGraph (stationaryConfiguration rule marks depth)).Reachable
          (rule.generation depth).network.source vertex →
        potential (rule.generationOldVertex depth vertex) = boundary vertex) ∧
      sourceComponentEnergy (network (rule.generation (depth + 1)).network (stationaryConfiguration rule marks (depth + 1)))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks (depth + 1)) potential =
      sourceComponentEnergy (network (rule.generation depth).network (stationaryConfiguration rule marks depth))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks depth) boundary

theorem stationaryHarmonicTypical_ae
    (growthPositive : 0 < growth)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks := by
  filter_upwards [stationaryEnergyTypical_ae rule p positive belowOne fixedPoint growth value growthPositive
      valuePositive fixed,
    actual_stationary_generation_source_minimizer rule p positive belowOne fixedPoint growth growthPositive
      value valuePositive fixed] with marks energy harmonic
  exact ⟨energy, fun depth boundary => harmonic depth [] true boundary⟩

variable (growthPositive : 0 < growth)
variable (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

def harmonicTypicalEnergyMarks :
    {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks} :=
  ⟨marks.val, marks.property.1⟩

def actualHarmonicFunction (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ) :
    ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ :=
  harmonicTowerFunction rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 initial boundary

theorem actualHarmonicFunction_finite (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ) :
    actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks initial boundary ∈
      energyDomain
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) :=
  harmonicTowerFunction_finite rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 marks.property.1.2 initial boundary

theorem actualHarmonicFunction_boundary (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (vertex : RetainedSkeletonVertex (rule.generation initial).network (stationaryConfiguration rule marks.val initial)) :
    actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks initial boundary
      (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 initial vertex) = boundary vertex.val :=
  harmonicTowerFunction_boundary rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 initial boundary vertex

theorem actualHarmonicFunction_limiting_energy (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ) :
    limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks initial boundary) =
    sourceComponentEnergy (network (rule.generation initial).network (stationaryConfiguration rule marks.val initial))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val initial) boundary :=
  harmonicTowerFunction_limiting_energy rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 marks.property.2 marks.property.1.2 initial boundary

end
end IGSIII34.ResistanceLimit
