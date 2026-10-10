import IGSIII.Geometry.CellLocalisationRelabelling
import IGSIII.Geometry.BoxDimensionCovering

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open scoped Topology NNReal ENNReal

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Actual indexed costs restrict to the indexed leaf in the selected cell. -/
theorem indexed_substitute_cell_cost_endpoint
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s(((outer.substitute inner).endpoint edge).1,
      ((outer.substitute inner).endpoint edge).2)))
    (values : Fin (outerEdges * innerEdges) → ℝ) (edge : Fin outerEdges) (child : Fin innerEdges) :
    cellBondCost outer inner
      (fun bond => indexedBondCost (outer.substitute inner) values (bond.map (Fintype.equivFin _))) edge
      s((inner.endpoint child).1, (inner.endpoint child).2) = values (finProdFinEquiv (edge, child)) := by
  change indexedBondCost (outer.substitute inner) values
    s(Fintype.equivFin _ (outer.cellVertex inner edge (inner.endpoint child).1),
      Fintype.equivFin _ (outer.cellVertex inner edge (inner.endpoint child).2)) = _
  have identity := indexedBondCost_endpoint (outer.substitute inner) simple values (finProdFinEquiv (edge, child))
  simpa only [outer.substitute_endpoint, Prod.fst, Prod.snd] using identity

theorem indexed_substitute_cell_edge_floor
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s(((outer.substitute inner).endpoint edge).1,
      ((outer.substitute inner).endpoint edge).2)))
    (values : Fin (outerEdges * innerEdges) → ℝ) (cells : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (floor : ℝ)
    (leaf_floor : ∀ child, cells edge child = true → floor ≤ values (finProdFinEquiv (edge, child))) :
    ∀ bond ∈ (inner.openGraph (cells edge)).edgeSet,
      floor ≤ cellBondCost outer inner
        (fun bond => indexedBondCost (outer.substitute inner) values (bond.map (Fintype.equivFin _))) edge bond := by
  intro bond
  refine Sym2.inductionOn bond (fun first last => ?_)
  intro adjacent
  change (inner.openGraph (cells edge)).Adj first last at adjacent
  obtain ⟨_, child, opened, endpoints | endpoints⟩ := adjacent
  · have bond_identity : s((inner.endpoint child).1, (inner.endpoint child).2) = s(first, last) := by rw [endpoints]
    rw [← bond_identity, indexed_substitute_cell_cost_endpoint outer inner simple]
    exact leaf_floor child opened
  · have bond_identity : s((inner.endpoint child).1, (inner.endpoint child).2) = s(first, last) := by rw [endpoints, Sym2.eq_swap]
    rw [← bond_identity, indexed_substitute_cell_cost_endpoint outer inner simple]
    exact leaf_floor child opened

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scale_positive : 0 < scale)
variable (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < limit_length depth edge)
variable (child_convergence : ∀ coarse edge, Filter.Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) Filter.atTop (nhds (limit_length coarse edge)))

/-- A successful connected-cell family yields an actual packing in the
completed chemical metric, by choosing retained first-generation interior
vertices. No packing statement is an input. -/
theorem actualChemicalSpace_packing_of_connected_cells {Index : Type*} [Fintype Index]
    (depth : ℕ) (indices : Index ↪ Fin (rule.generation depth).edges)
    (retained : ∀ index, configuration depth (indices index) = true)
    (attached : ∀ index, ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source ((rule.generation depth).network.endpoint (indices index)).1)
    (floor : ℝ) (floor_positive : 0 < floor)
    (leaf_floor : ∀ index child,
      configuration (depth + 1) (finProdFinEquiv (indices index, child)) = true →
        floor ≤ limit_length (depth + 1) (finProdFinEquiv (indices index, child))) :
    (Fintype.card Index : ℕ∞) ≤ Metric.coveringNumber
      ⟨floor / 2, (div_pos floor_positive (by norm_num)).le⟩
      (Set.univ : Set (ActualChemicalSpace rule classicalRule configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence)) := by
  classical
  let cells : Fin (rule.generation depth).edges → Configuration rule.edges :=
    substitutionConfigurationEquiv.symm (configuration (depth + 1))
  have cell_crosses (index : Index) : rule.network.crosses (cells (indices index)) = true := by
    have compatibility := congrFun (coherent depth) (indices index)
    change rule.network.crosses (cells (indices index)) = configuration depth (indices index) at compatibility
    exact compatibility.trans (retained index)
  have internal_exists (index : Index) := exists_retained_internal_vertex rule.network classicalRule.scale
    (cells (indices index)) (cell_crosses index)
  choose point not_source not_target point_reached using internal_exists
  let vertex (index : Index) : Fin (rule.generation (depth + 1)).vertices :=
    Fintype.equivFin _ ((rule.generation depth).network.cellVertex rule.network (indices index) (point index))
  let iso := (rule.generation depth).network.substitutionGraphIso rule.network cells
  have configuration_eq : substitutionConfigurationEquiv cells = configuration (depth + 1) :=
    substitutionConfigurationEquiv.apply_symm_apply _
  have vertex_reached (index : Index) :
      ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
        (rule.generation (depth + 1)).network.source (vertex index) := by
    have old_reached := (retainedOldVertexEmbedding rule configuration coherent depth
      ⟨((rule.generation depth).network.endpoint (indices index)).1, attached index⟩).property
    have child_reached := ((point_reached index).map
      ((rule.generation depth).network.cellHom rule.network cells (indices index))).map iso.toHom
    change ((rule.generation (depth + 1)).network.openGraph (substitutionConfigurationEquiv cells)).Reachable
      (Fintype.equivFin _ ((rule.generation depth).network.cellVertex rule.network (indices index) rule.network.source))
      (vertex index) at child_reached
    rw [configuration_eq, (rule.generation depth).network.cellVertex_source] at child_reached
    exact old_reached.trans child_reached
  let points (index : Index) := actualChemicalVertex rule classicalRule configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence (depth + 1) ⟨vertex index, vertex_reached index⟩
  apply finite_separated_le_coveringNumber points
  intro first second distinct
  have cell_distinct : indices first ≠ indices second := fun equal => distinct (indices.injective equal)
  let cost (bond : Sym2 ((rule.generation depth).network.SubstitutionVertex rule.network)) : ℝ :=
    indexedBondCost (rule.generation (depth + 1)).network (limit_length (depth + 1)) (bond.map (Fintype.equivFin _))
  have cost_nonnegative : ∀ bond, 0 ≤ cost bond := fun bond =>
    indexedBondCost_nonnegative _ _ (nonnegative (depth + 1)) _
  have boundary_floor (index : Index) : floor ≤ weightedComponentBoundaryDistance
      (rule.network.openGraph (cells (indices index)))
      (cellBondCost (rule.generation depth).network rule.network cost (indices index))
      rule.network.source rule.network.target (point index) := by
    apply weightedComponentBoundaryDistance_ge_edge_floor _ _ floor floor_positive.le
      (indexed_substitute_cell_edge_floor (rule.generation depth).network rule.network
        (classicalRule.generation (depth + 1)).simple (limit_length (depth + 1)) cells (indices index)
        floor (leaf_floor index)) _ _ _ (not_source index) (not_target index) (Or.inl (point_reached index))
  have actual_reachable := (vertex_reached first).symm.trans (vertex_reached second)
  rw [← configuration_eq] at actual_reachable
  have separation := weighted_distinct_cells_boundary_separation (rule.generation depth).network rule.network cells
    cost cost_nonnegative (indices first) (indices second) cell_distinct (point first) (point second)
    (iso.reachable_iff.mp actual_reachable)
  have identity := weightedDistance_graphIso iso
    (indexedBondCost (rule.generation (depth + 1)).network (limit_length (depth + 1)))
    (indexedBondCost_nonnegative _ _ (nonnegative (depth + 1)))
    ((rule.generation depth).network.cellVertex rule.network (indices first) (point first))
    ((rule.generation depth).network.cellVertex rule.network (indices second) (point second))
  change weightedDistance ((rule.generation (depth + 1)).network.openGraph (substitutionConfigurationEquiv cells))
    (indexedBondCost (rule.generation (depth + 1)).network (limit_length (depth + 1)))
    (vertex first) (vertex second) = weightedDistance
      ((rule.generation depth).network.substitutedGraph rule.network cells) cost
      ((rule.generation depth).network.cellVertex rule.network (indices first) (point first))
      ((rule.generation depth).network.cellVertex rule.network (indices second) (point second)) at identity
  rw [configuration_eq] at identity
  dsimp only [points]
  rw [actualChemicalVertex_distance, identity]
  have first_bound := boundary_floor first
  have second_bound := boundary_floor second
  change 2 * (floor / 2) < _
  linarith

end
end IGSIII.Geometry


