import IGSIII.Geometry.RootedComponentAnchors
import IGSIII.Geometry.CellLocalisationInnerRadius

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (scale : ℝ) (scalePositive : 0 < scale) (offset : ℕ)
variable (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ values depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < values depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + offset)) atTop (𝓝 (values coarse edge)))

/-- An actual crossing component contains an intrinsic point at strictly
positive distance from both planted boundary points. This is a deterministic
consequence of the first actual crossing graph and its positive edge lengths. -/
theorem rootedComponentSpace_positive_interior_radius
    (crossing : (rule.generation 0).network.crosses (configuration 0) = true) :
    ∃ point : RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive offset
      values nonnegative positive childConvergence,
      0 < min
        (dist point (rootedFirstBoundaryAnchor rule classicalRule configuration coherent sourceSide scale scalePositive offset
          values nonnegative positive childConvergence))
        (dist point (rootedSecondBoundaryAnchor rule classicalRule configuration coherent sourceSide scale scalePositive offset
          values nonnegative positive childConvergence)) := by
  classical
  obtain ⟨vertex, notSource, notTarget, sourceReached⟩ := exists_retained_internal_vertex
    (rule.generation 0).network (classicalRule.generation 0).scale (configuration 0) crossing
  have terminalReachable := ((rule.generation 0).network.crosses_eq_true (configuration 0)).mp crossing
  have targetReached := terminalReachable.symm.trans sourceReached
  have retained : ((rule.generation 0).network.openGraph (configuration 0)).Reachable
      (plantedVertex (rule.generation 0).network sourceSide) vertex := by
    cases sourceSide with
    | false => exact targetReached
    | true => exact sourceReached
  have sourcePositive : 0 < weightedDistance ((rule.generation 0).network.openGraph (configuration 0))
      (indexedBondCost (rule.generation 0).network (values 0)) (rule.generation 0).network.source vertex := by
    apply lt_of_le_of_ne (weightedDistance_nonneg _ _ (indexedBondCost_nonnegative _ _ (nonnegative 0)) _ _)
    intro zeroDistance
    exact notSource (eq_of_weightedDistance_eq_zero_of_edge_positive _ _
      (indexedBondCost_nonnegative _ _ (nonnegative 0))
      (indexedBondCost_positive_on_open_edges _ (classicalRule.generation 0).simple _ _ (positive 0))
      sourceReached zeroDistance.symm).symm
  have targetPositive : 0 < weightedDistance ((rule.generation 0).network.openGraph (configuration 0))
      (indexedBondCost (rule.generation 0).network (values 0)) (rule.generation 0).network.target vertex := by
    apply lt_of_le_of_ne (weightedDistance_nonneg _ _ (indexedBondCost_nonnegative _ _ (nonnegative 0)) _ _)
    intro zeroDistance
    exact notTarget (eq_of_weightedDistance_eq_zero_of_edge_positive _ _
      (indexedBondCost_nonnegative _ _ (nonnegative 0))
      (indexedBondCost_positive_on_open_edges _ (classicalRule.generation 0).simple _ _ (positive 0))
      targetReached zeroDistance.symm).symm
  refine ⟨rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset
    values nonnegative positive childConvergence 0 ⟨vertex, retained⟩, ?_⟩
  rw [rootedComponentBoundary_radius]
  simpa only [weightedComponentBoundaryDistance, if_pos sourceReached, if_pos targetReached] using
    lt_min sourcePositive targetPositive

end
end IGSIII.Geometry


