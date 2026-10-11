import IGSIII34.ResistanceLimit.CellPreservedEnergy
import IGSIII34.ResistanceLimit.StationaryBlockResponseCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution
open scoped BigOperators

/-- A stationary block has a fixed boundary-test energy at every refinement.
The finite sum on the right is independent of the refinement depth. -/
theorem stationary_block_boundary_test_energy
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    {outerVertices outerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (addresses : Fin outerEdges → List (Fin rule.edges)) (coarse : Configuration outerEdges)
    (fine : ℕ) (scalar : ℝ) (scalarPositive : 0 < scalar) (chosen : Fin outerEdges) :
    cellBoundaryTestEnergy outer (rule.generation fine).network
      (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))
      (fun edge => scalar * stationaryGenerationResistance rule field growth fine (addresses edge.1) edge.2.val)
      chosen =
      ∑ edge, if coarse edge = true then
        (cellBoundaryIndicator outer chosen (outer.endpoint edge).1 -
          cellBoundaryIndicator outer chosen (outer.endpoint edge).2) ^ 2 /
          (scalar * field (addresses edge)) else 0 := by
  classical
  unfold cellBoundaryTestEnergy coarsePotentialEnergy
  apply Finset.sum_congr rfl
  intro edge _
  unfold cellTraceEnergy
  rw [markedGenerationConfiguration_crosses rule marks crossing]
  by_cases opened : coarse edge = true
  · simp only [if_pos opened]
    change _ / electricalCell (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))
      (fun child => scalar * stationaryGenerationResistance rule field growth fine (addresses edge) child) = _
    have weightsNonnegative : ∀ child : Fin (rule.generation fine).edges,
        0 ≤ stationaryGenerationResistance rule field growth fine (addresses edge) child :=
      fun child => (mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)).le
    rw [opened, electricalCell_scale (rule.generation fine).network _ weightsNonnegative
      scalarPositive.le,
      stationary_field_normalized_block_response rule marks field growth growthPositive
        fieldPositive crossing stationary]
  · simp [opened]

end
end IGSIII34.ResistanceLimit
