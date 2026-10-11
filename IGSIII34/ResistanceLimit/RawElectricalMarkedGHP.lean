import IGSIII34.ResistanceLimit.RawElectricalCommonRealisation
import IGSIII34.Topology.ProjectionMarkedGHP
import IGSIII.Chemical.SmallBall.ActualChemicalTerminals

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

instance rawElectricalFiniteClusterMeasurableSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ) :
    MeasurableSpace (RawElectricalFiniteCluster rule configuration growth growthPositive depth) := ⊤

instance rawElectricalFiniteClusterBorelSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ) :
    BorelSpace (RawElectricalFiniteCluster rule configuration growth growthPositive depth) :=
  ⟨borel_eq_top_of_countable.symm⟩

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})

local instance rawElectricalMarkedGHPMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance rawElectricalMarkedGHPBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

def rawElectricalTerminal (depth : ℕ) (side : Bool) :
    RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth :=
  retainedTerminalVertex rule (stationaryConfiguration rule marks.val)
    (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true) depth side

def actualElectricalTerminal (side : Bool) :
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks :=
  actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks 0
    (rawElectricalTerminal rule p positive belowOne fixedPoint growth value growthPositive marks 0 side)

theorem actual_electrical_terminal_birth_identity (depth : ℕ) (side : Bool) :
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth
      (rawElectricalTerminal rule p positive belowOne fixedPoint growth value growthPositive marks depth side) =
        actualElectricalTerminal rule p positive belowOne fixedPoint growth value growthPositive marks side := by
  have persistent := electricalVertex_persistent rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    marks.property.2.2 0 depth (Nat.zero_le depth)
    (retainedTerminalVertex rule (stationaryConfiguration rule marks.val)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true) 0 side)
  rw [retainedPersistentVertexEmbedding_terminal] at persistent
  exact persistent.symm

theorem actual_raw_electrical_markedGHP
    [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (sourceMeasure : ∀ depth, Measure (RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth))
    (targetMeasure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks))
    (measureConvergence : Tendsto (fun depth => levyProkhorovEDist
      ((sourceMeasure depth).map (fun vertex : RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)) targetMeasure)
      atTop (𝓝 0)) :
    MarkedGHPConverges
      (fun depth => RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth)
      sourceMeasure targetMeasure
      (rawElectricalTerminal rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualElectricalTerminal rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  apply IGSIII34.Topology.markedGHPConverges_of_uniform_projection
    (fun depth => RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth)
    sourceMeasure targetMeasure
    (rawElectricalTerminal rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualElectricalTerminal rule p positive belowOne fixedPoint growth value growthPositive marks)
    (fun depth vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)
    (fun _ => measurable_of_finite _)
    (actual_raw_electrical_birth_uniform_distortion rule p positive belowOne fixedPoint growth value growthPositive marks
      fieldLimit eta coefficient start etaNonnegative etaBelowOne radiusBounds)
    (actual_electrical_birth_eventually_net rule p positive belowOne fixedPoint growth value growthPositive marks)
    measureConvergence
    (actual_electrical_terminal_birth_identity rule p positive belowOne fixedPoint growth value growthPositive marks)

end
end IGSIII34.ResistanceLimit
