import IGSIII.ActualChemicalCellRouteEquality
import IGSIII.Geometry.CellLocalisationDiscrete
import IGSIII.Geometry.ActualBlockCellEmbedding
import IGSIII.Geometry.RootedComponentSkeleton
import Universality.Graph.GenerationInternalNeighborhood

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- The actual unweighted intrinsic component metric, without imposing any
connectivity on vertices outside the selected component. -/
@[reducible] def retainedUnitChemicalMetric {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges) (sourceSide : Bool) :
    MetricSpace (RetainedComponentVertex network configuration sourceSide) where
  dist first last := weightedDistance (network.openGraph configuration) (fun _ => 1) first.val last.val
  dist_self first := weightedDistance_self _ _ (fun _ => zero_le_one) first.val
  dist_comm first last := weightedDistance_comm _ _ (fun _ => zero_le_one) first.val last.val
  dist_triangle first middle last := weightedDistance_triangle _ _ (fun _ => zero_le_one)
    (first.property.symm.trans middle.property) (middle.property.symm.trans last.property)
  eq_of_dist_eq_zero := fun {first last} zeroDistance => Subtype.ext
    (eq_of_weightedDistance_eq_zero _ _ (fun _ => zero_lt_one)
      (first.property.symm.trans last.property) zeroDistance)

/-- The two planted boundary vertices of a retained component. For a
noncrossing component the second entry repeats the first. -/
def retainedChemicalBoundaryVertex {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (sourceSide side : Bool) : RetainedComponentVertex network configuration sourceSide := by
  classical
  exact if side then
    if connected : (network.openGraph configuration).Reachable (plantedVertex network sourceSide)
        (plantedVertex network (!sourceSide)) then
      ⟨plantedVertex network (!sourceSide), connected⟩
    else ⟨plantedVertex network sourceSide, SimpleGraph.Reachable.refl _⟩
  else ⟨plantedVertex network sourceSide, SimpleGraph.Reachable.refl _⟩

theorem retainedChemicalBoundary_excludes_terminals {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (sourceSide : Bool) (point : RetainedComponentVertex network configuration sourceSide)
    (interior : ∀ side, point ≠ retainedChemicalBoundaryVertex network configuration sourceSide side) :
    point.val ≠ network.source ∧ point.val ≠ network.target := by
  classical
  have ownDistinct : point.val ≠ plantedVertex network sourceSide := by
    intro same
    exact interior false (Subtype.ext same)
  have otherDistinct : point.val ≠ plantedVertex network (!sourceSide) := by
    intro same
    have connected : (network.openGraph configuration).Reachable (plantedVertex network sourceSide)
        (plantedVertex network (!sourceSide)) := by
      simpa only [same] using point.property
    apply interior true
    apply Subtype.ext
    simpa only [retainedChemicalBoundaryVertex, Bool.true_eq, ↓reduceIte, dif_pos connected] using same
  cases sourceSide with
  | false =>
    simpa only [plantedVertex, Bool.not_false, Bool.false_eq_true, ↓reduceIte] using
      (show point.val ≠ plantedVertex network (!false) ∧ point.val ≠ plantedVertex network false from
        ⟨otherDistinct, ownDistinct⟩)
  | true =>
    simpa only [plantedVertex, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using
      (show point.val ≠ plantedVertex network true ∧ point.val ≠ plantedVertex network (!true) from
        ⟨ownDistinct, otherDistinct⟩)


/-- Indexed microscopic cell edges cannot leave through an interior vertex. -/
theorem generationBlockCellEmbedding_internal_neighbor (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges)
    (vertex : (rule.generation fine).network.InteriorVertex)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (neighbor : Fin (rule.generation (coarse + fine + 1)).vertices)
    (adjacent : ((rule.generation (coarse + fine + 1)).network.openGraph configuration).Adj
      ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex.val) neighbor) :
    ∃ inside, (generationBlockCellEmbedding rule coarse fine edge).vertex inside = neighbor ∧
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Adj vertex.val inside := by
  apply (generationBlockCellEmbedding rule coarse fine edge).neighbor_lifts_of_incident_edges vertex.val
    (fun bond incident => ?_) configuration neighbor adjacent
  exact ((rule.generation coarse).network.cellNetworkEmbedding (rule.generation fine).network edge).trans_equivalence_incident_edges
    (rule.generationBlockDecomposition coarse fine).symm vertex.val
    ((rule.generation coarse).network.cell_internal_incident_edge (rule.generation fine).network edge vertex) bond incident

/-- Literal four-route formula on every actual microscopic retained block. -/
theorem generationBlockCellEmbedding_route_equality (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (first last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration edge) sourceSide) :
    letI := retainedUnitChemicalMetric (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration edge) sourceSide
    weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph configuration) (fun _ => 1)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex first.val)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex last.val) =
      twoBoundaryWeightedRouteDistance
        ((rule.generation (coarse + fine + 1)).network.openGraph configuration) (fun _ => 1)
        (fun point => (generationBlockCellEmbedding rule coarse fine edge).vertex point.val)
        (retainedChemicalBoundaryVertex (rule.generation fine).network
          (generationBlockCells rule coarse fine configuration edge) sourceSide) first last := by
  letI := retainedUnitChemicalMetric (rule.generation fine).network
    (generationBlockCells rule coarse fine configuration edge) sourceSide
  refine weighted_graph_two_boundary_route_direct_equality
    ((rule.generation (coarse + fine + 1)).network.openGraph configuration) (fun _ => 1) (fun _ => zero_le_one)
    (fun point : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration edge) sourceSide =>
        (generationBlockCellEmbedding rule coarse fine edge).vertex point.val)
    (fun _ _ same => Subtype.ext ((generationBlockCellEmbedding rule coarse fine edge).vertex.injective same))
    ?_ ?_ (retainedChemicalBoundaryVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration edge) sourceSide) ?_ first last
  · intro first last
    change weightedDistance _ (fun _ => 1) _ _ ≤ weightedDistance _ (fun _ => 1) _ _
    simp only [weightedDistance_unit_eq_dist]
    exact_mod_cast generationBlockCellEmbedding_distance_le rule coarse fine edge configuration first.val last.val
      (first.property.symm.trans last.property)
  · intro first last
    exact (first.property.symm.trans last.property).map
      ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom configuration)
  · intro point interior neighbor adjacent
    have terminals := retainedChemicalBoundary_excludes_terminals (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration edge) sourceSide point interior
    obtain ⟨inside, insideIdentity, insideAdjacent⟩ := generationBlockCellEmbedding_internal_neighbor
      rule coarse fine edge ⟨point.val, terminals⟩ configuration neighbor adjacent
    refine ⟨⟨inside, point.property.trans insideAdjacent.reachable⟩, insideIdentity, ?_⟩
    change weightedDistance _ (fun _ => 1) point.val inside ≤ 1
    simpa only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      weightedDistance_le_walkCost _ (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
        (SimpleGraph.Walk.cons insideAdjacent SimpleGraph.Walk.nil)

end
end IGSIII.Geometry
