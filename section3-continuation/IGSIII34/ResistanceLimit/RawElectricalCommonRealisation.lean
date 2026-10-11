import IGSIII34.ResistanceLimit.RawElectricalBirthDistortion
import IGSIII34.Topology.IncreasingDenseNets
import IGSIII34.Topology.CommonProjectionMetricRealisationCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]

theorem actual_electrical_birth_eventually_net (radius : ℝ) (radiusPositive : 0 < radius) :
    ∀ᶠ depth in atTop, ∀ point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks,
      ∃ vertex : RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth,
        dist point (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex) < radius := by
  have nested : Monotone (fun depth => Set.range
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth)) := by
    apply monotone_nat_of_le_succ
    intro depth point member
    obtain ⟨vertex, rfl⟩ := member
    refine ⟨retainedOldVertexEmbedding rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks) depth vertex, ?_⟩
    exact (electricalVertex_old rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
      marks.property.2.2 depth vertex).symm
  filter_upwards [IGSIII34.Topology.increasing_dense_sets_eventually_net _ nested
    (actualStationaryElectricalVertex_dense rule p positive belowOne fixedPoint growth value growthPositive marks)
    radius radiusPositive] with depth net
  intro point
  obtain ⟨anchor, ⟨vertex, rfl⟩, close⟩ := net point
  exact ⟨vertex, close⟩

theorem exists_actual_raw_electrical_common_isometric_realisation
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length) :
    ∃ (Ambient : Type) (ambientMetric : MetricSpace Ambient),
      letI := ambientMetric
      CompleteSpace Ambient ∧ CompactSpace Ambient ∧
      ∃ target : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks → Ambient,
        Isometry target ∧
      ∃ sources : ∀ depth, RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth → Ambient,
        (∀ depth, Isometry (sources depth)) ∧
        ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ point,
          dist (sources depth point) (target
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth point)) < tolerance := by
  letI : ∀ depth, Fintype (RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth) :=
    fun _ => Fintype.ofFinite _
  letI : Nonempty (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) :=
    ⟨actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks 0
      ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩⟩
  exact IGSIII34.Topology.exists_common_isometric_realisation_of_uniform_projection_distortion_completion20261011
    (fun depth => RawElectricalFiniteCluster rule (stationaryConfiguration rule marks.val) growth growthPositive depth)
    (fun depth vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)
    (actual_raw_electrical_birth_uniform_distortion rule p positive belowOne fixedPoint growth value growthPositive marks
      fieldLimit eta coefficient start etaNonnegative etaBelowOne radiusBounds)

end
end IGSIII34.ResistanceLimit
