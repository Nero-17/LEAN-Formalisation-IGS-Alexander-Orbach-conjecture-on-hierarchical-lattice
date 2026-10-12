import IGSIII34.Forms.CompletionLocalityCompletion
import IGSIII34.Forms.ActualRegularityCompletion
import IGSIII34.Forms.StationaryWeightMesh

/-! Strong locality of the actual full retained trace form. Dangling edges
are retained; only components disconnected from the source have coefficient
zero. The mesh is the proved stationary generation weight mesh. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

theorem actualConductance_inverse_eq_stationaryResistance (depth : ℕ) (edge)
    (conductive : actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) depth edge ≠ 0) :
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) depth edge)⁻¹ =
      stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth edge := by
  unfold actualEnergyConductance skeletonEnergyConductance at conductive ⊢
  split_ifs at conductive ⊢ <;> simp_all [harmonicTypicalEnergyMarks]

theorem actualCompletionPairing_strongly_local
    (eta : ℝ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (weightMesh : ∃ threshold : ℕ, ∀ depth, threshold ≤ depth + 1 → ∀ edge,
      stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth edge ≤ eta ^ (depth + 1))
    {first second : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)), ℝ)}
    (firstFinite : first ∈ actualCompletionEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks)
    (secondFinite : second ∈ actualCompletionEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks)
    (neighborhood : Set (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne
      fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))))
    (openNeighborhood : IsOpen neighborhood)
    (supportCompact : IsCompact (closure (Function.support (second : _ → ℝ))))
    (supportSubset : closure (Function.support (second : _ → ℝ)) ⊆ neighborhood)
    (constant : ∀ firstPoint ∈ neighborhood, ∀ secondPoint ∈ neighborhood,
      first firstPoint = first secondPoint) :
    limitingPairing
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (fun point : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) =>
          first (UniformSpace.Completion.coe' point))
      (fun point : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) =>
          second (UniformSpace.Completion.coe' point)) = 0 := by
  apply completionLimitingPairing_strongly_local_of_eventual_mesh
    (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_skeleton_resistance_attained rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (fun depth => eta ^ (depth + 1))
    ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1))
    ?_ firstFinite secondFinite neighborhood openNeighborhood supportCompact supportSubset constant
  obtain ⟨threshold, bounds⟩ := weightMesh
  filter_upwards [eventually_ge_atTop threshold] with depth after
  intro edge conductive
  rw [actualConductance_inverse_eq_stationaryResistance rule p positive belowOne fixedPoint growth value marks depth edge conductive]
  exact bounds depth (after.trans (Nat.le_succ depth)) edge

end
end IGSIII34.Forms
