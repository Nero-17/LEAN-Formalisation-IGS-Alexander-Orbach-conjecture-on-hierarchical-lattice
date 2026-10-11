import IGSIII34.ResistanceLimit.ActualBlockElectricalCompletion20261011
import IGSIII.Geometry.ActualComponentBoundary

set_option autoImplicit false
set_option maxHeartbeats 2800000
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
  (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
  (typical : StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks)

instance electricalBoundarySpaceMeasurableSpace : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩) := borel _
instance electricalBoundarySpaceBorelSpace : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩) := ⟨rfl⟩
instance electricalBoundarySpaceNonempty : Nonempty
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩) :=
  ⟨actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ 0
    ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩⟩

def actualElectricalComponentWordPoint (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ :=
  if live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive then
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ depth
      ⟨componentWordAnchor rule marks depth word, componentWordAnchor_retained rule marks typical.2.1 depth word live⟩
  else actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ 0
    ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩

theorem actualElectricalComponentWordPoint_successor_distance
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop
        (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks)))
    (depth : ℕ) (word : Fin (depth + 2) → (Fin rule.edges × Bool))
    (parentLive : retainedComponentState rule marks (List.ofFn (Fin.init word)) ≠ .inactive)
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive)
    (bound : ℝ)
    (microscopicBound : ∀ host (point : Fin (rule.generation host).vertices),
      ((rule.generation host).network.openGraph
        (generationBlockCells rule depth host (stationaryConfiguration rule marks (depth + host + 1))
          (generationWordEdge rule depth (fun index => (Fin.init word index).1)))).Reachable
            (plantedVertex (rule.generation host).network
              (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected) point →
      pairResistance (network (rule.generation (depth + host + 1)).network
          (stationaryConfiguration rule marks (depth + host + 1))) (fun _ => 1)
        ((generationBlockCellEmbedding rule depth host
          (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex
          (plantedVertex (rule.generation host).network
            (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected))
        ((generationBlockCellEmbedding rule depth host
          (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex point) /
            growth ^ (depth + host + 2) ≤ bound) :
    dist (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks typical depth (Fin.init word))
      (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks typical (depth + 1) word) ≤ bound := by
  have bitIdentity : markedGenerationConfiguration rule marks depth [] true
      (generationWordEdge rule depth (fun index => (Fin.init word index).1)) =
        (retainedComponentState rule marks (List.ofFn (Fin.init word))).massOpened :=
    generationWordEdge_massOpened rule marks depth [] .connected (Fin.init word) parentLive
  have addressIdentity : generationEdgeAddress rule depth
      (generationWordEdge rule depth (fun index => (Fin.init word index).1)) =
        componentEdgeAddress (List.ofFn (Fin.init word)) := by
    rw [generationWordEdge_address]
    simp only [componentEdgeAddress, List.map_ofFn, Function.comp_def]
  have configurationIdentity : generationBlockCells rule depth 0
      (stationaryConfiguration rule marks (depth + 0 + 1))
      (generationWordEdge rule depth (fun index => (Fin.init word index).1)) =
        marks (componentEdgeAddress (List.ofFn (Fin.init word)),
          (retainedComponentState rule marks (List.ofFn (Fin.init word))).massOpened) := by
    rw [stationaryConfiguration, generationBlockCells_marked, List.nil_append, addressIdentity, bitIdentity]
    rfl
  have childReachable := componentWordAnchor_child_reachable rule marks typical.2.1 depth word parentLive live
  have reachable : ((rule.generation 0).network.openGraph
      (generationBlockCells rule depth 0 (stationaryConfiguration rule marks (depth + 0 + 1))
        (generationWordEdge rule depth (fun index => (Fin.init word index).1)))).Reachable
      (plantedVertex (rule.generation 0).network
        (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected)
      (if (retainedComponentState rule marks (List.ofFn word)).sourceSelected then
        (rule.network.endpoint (word (Fin.last (depth + 1))).1).1
      else (rule.network.endpoint (word (Fin.last (depth + 1))).1).2) := by
    change (rule.network.openGraph _).Reachable (plantedVertex rule.network _) _
    rw [configurationIdentity]
    exact childReachable
  have inherited := (retainedOldVertexEmbedding rule (stationaryConfiguration rule marks)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩) depth
      ⟨_, componentWordAnchor_retained rule marks typical.2.1 depth (Fin.init word) parentLive⟩).property
  have anchorRetained : ((rule.generation (depth + 1)).network.openGraph
      (stationaryConfiguration rule marks (depth + 1))).Reachable
        (rule.generation (depth + 1)).network.source
        ((generationBlockCellEmbedding rule depth 0
          (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex
          (plantedVertex rule.network (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected)) := by
    rw [componentWordAnchor_block_parent]
    exact inherited
  have vertexRetained := componentWordAnchor_retained rule marks typical.2.1 (depth + 1) word live
  rw [componentWordAnchor_bottom] at vertexRetained
  have estimate := actualElectricalVertex_dist_block_le rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks, typical⟩ fieldLimit depth 0
    (generationWordEdge rule depth (fun index => (Fin.init word index).1))
    (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected _ reachable
    anchorRetained vertexRetained bound microscopicBound
  rw [actualElectricalComponentWordPoint, dif_pos parentLive, actualElectricalComponentWordPoint, dif_pos live]
  change dist (electricalVertex _ _ _ _ _ _ depth _) (electricalVertex _ _ _ _ _ _ (depth + 1) _) ≤ _
  rw [electricalVertex_old]
  convert estimate using 1
  congr 2
  · apply Subtype.ext
    exact (componentWordAnchor_block_parent rule marks depth word).symm
  · apply Subtype.ext
    exact componentWordAnchor_bottom rule marks depth word

theorem exists_actual_electrical_component_boundary_pushforward
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop
        (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (retainedPaths : ∀ᵐ path ∂boundary, ∀ depth,
      Fin.init (path (depth + 1)) = path depth ∧
        retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive)
    (eta coefficient : ℝ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient) (start : ℕ)
    (microscopicMesh : ∀ coarse fine (edge : Fin (rule.generation coarse).edges) side
      (vertex : Fin (rule.generation fine).vertices), start ≤ coarse →
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (stationaryConfiguration rule marks (coarse + fine + 1)) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      pairResistance (network (rule.generation (coarse + fine + 1)).network
          (stationaryConfiguration rule marks (coarse + fine + 1))) (fun _ => 1)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) /
          growth ^ (coarse + fine + 2) ≤ coefficient * eta ^ (coarse + 1)) :
    ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩,
      Measurable realization ∧ IsProbabilityMeasure (boundary.map realization) ∧
      (∀ᵐ path ∂boundary, Tendsto (fun depth => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
        growth value growthPositive marks typical depth (path (depth + 1))) atTop (𝓝 (realization path))) ∧
      (∀ depth, ∀ᵐ path ∂boundary, dist
        (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks typical
          (depth + start) (path (depth + start + 1)))
        (realization path) ≤ coefficient * eta ^ (start + 1) * eta ^ depth / (1 - eta)) ∧
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value
          growthPositive marks typical depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0) := by
  apply exists_measurable_geometric_boundary_limit boundary
    (fun depth path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
      marks typical depth (path (depth + 1)))
    (fun depth => (measurable_of_finite (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value
      growthPositive marks typical depth)).comp (measurable_pi_apply (depth + 1)))
    eta (coefficient * eta ^ (start + 1)) etaNonnegative etaBelowOne
    (mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _)) start
  filter_upwards [retainedPaths] with path retained
  intro depth
  have parentLive : retainedComponentState rule marks (List.ofFn (Fin.init (path (depth + start + 2)))) ≠ .inactive := by
    rw [(retained (depth + start + 1)).1]
    exact (retained (depth + start + 1)).2
  have estimate := actualElectricalComponentWordPoint_successor_distance rule p positive belowOne fixedPoint growth value
    growthPositive marks typical fieldLimit (depth + start) (path (depth + start + 2)) parentLive
    (retained (depth + start + 2)).2 (coefficient * eta ^ (depth + start + 1))
    (fun host point reachable => microscopicMesh (depth + start) host _ _ point (by omega) reachable)
  simpa only [(retained (depth + start + 1)).1, Nat.add_assoc, Nat.add_comm depth start,
    pow_add, mul_assoc, mul_comm, mul_left_comm] using estimate

end
end IGSIII34.ResistanceLimit
