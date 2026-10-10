import IGSIII.Geometry.ComponentWordAnchors
import IGSIII.Geometry.GeometricBoundaryRealization
import IGSIII.Mass.ComponentBoundaryLaw

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology

variable (rule : Rule) (classicalRule : rule.Classical)
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
variable (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
variable (scale : ℝ) (scale_positive : 0 < scale)
variable (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
variable (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < limit_length depth edge)
variable (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge)))

instance actualMarkedChemicalSpaceMeasurableSpace : MeasurableSpace
    (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scale_positive limit_length nonnegative positive child_convergence) := borel _

instance actualMarkedChemicalSpaceBorelSpace : BorelSpace
    (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scale_positive limit_length nonnegative positive child_convergence) := ⟨rfl⟩

/-- A cylinder representative is its actual retained selected endpoint.
The value on inactive words is a fixed actual root vertex. -/
def actualComponentWordPoint (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scale_positive limit_length nonnegative positive child_convergence :=
  if live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive then
    actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scale_positive limit_length nonnegative positive child_convergence depth
        ⟨componentWordAnchor rule marks depth word, componentWordAnchor_retained rule marks crossing depth word live⟩
  else actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scale_positive limit_length nonnegative positive child_convergence 0
      ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩

theorem componentWordAnchor_block_parent (depth : ℕ)
    (word : Fin (depth + 2) → (Fin rule.edges × Bool)) :
    (generationBlockCellEmbedding rule depth 0
      (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex
        (plantedVertex rule.network (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected) =
      rule.generationOldVertex depth (componentWordAnchor rule marks depth (Fin.init word)) := by
  unfold componentWordAnchor
  cases side : (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected <;>
    simp only [plantedVertex, Bool.false_eq_true, ↓reduceIte]
  · exact generationBlockCellEmbedding_target rule depth 0 _
  · exact generationBlockCellEmbedding_source rule depth 0 _

theorem actualComponentWordPoint_successor_distance (depth : ℕ)
    (word : Fin (depth + 2) → (Fin rule.edges × Bool))
    (parent_live : retainedComponentState rule marks (List.ofFn (Fin.init word)) ≠ .inactive)
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive)
    (bound : ℝ)
    (microscopic_bound : ∀ host (point : Fin (rule.generation host).vertices),
      ((rule.generation host).network.openGraph
        (generationBlockCells rule depth host (markedGenerationConfiguration rule marks (depth + host + 1) [] true)
          (generationWordEdge rule depth (fun index => (Fin.init word index).1)))).Reachable
            (plantedVertex (rule.generation host).network
              (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected) point →
      (((rule.generation (depth + host + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (depth + host + 1) [] true)).dist
          ((generationBlockCellEmbedding rule depth host (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex
            (plantedVertex (rule.generation host).network
              (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected))
          ((generationBlockCellEmbedding rule depth host (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex point) : ℝ) /
          scale ^ (depth + host + 2) ≤ bound) :
    dist (actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive limit_length
      nonnegative positive child_convergence depth (Fin.init word))
      (actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive limit_length
        nonnegative positive child_convergence (depth + 1) word) ≤ bound := by
  have bit_identity : markedGenerationConfiguration rule marks depth [] true
      (generationWordEdge rule depth (fun index => (Fin.init word index).1)) =
        (retainedComponentState rule marks (List.ofFn (Fin.init word))).massOpened :=
    generationWordEdge_massOpened rule marks depth [] .connected (Fin.init word) parent_live
  have address_identity : generationEdgeAddress rule depth
      (generationWordEdge rule depth (fun index => (Fin.init word index).1)) =
        componentEdgeAddress (List.ofFn (Fin.init word)) := by
    rw [generationWordEdge_address]
    simp only [componentEdgeAddress, List.map_ofFn, Function.comp_def]
  have configuration_identity : generationBlockCells rule depth 0
      (markedGenerationConfiguration rule marks (depth + 0 + 1) [] true)
      (generationWordEdge rule depth (fun index => (Fin.init word index).1)) =
      marks (componentEdgeAddress (List.ofFn (Fin.init word)),
        (retainedComponentState rule marks (List.ofFn (Fin.init word))).massOpened) := by
    rw [generationBlockCells_marked, List.nil_append, address_identity, bit_identity]
    rfl
  have child_reachable := componentWordAnchor_child_reachable rule marks crossing depth word parent_live live
  have reachable : ((rule.generation 0).network.openGraph
      (generationBlockCells rule depth 0 (markedGenerationConfiguration rule marks (depth + 0 + 1) [] true)
        (generationWordEdge rule depth (fun index => (Fin.init word index).1)))).Reachable
      (plantedVertex (rule.generation 0).network
        (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected)
      (if (retainedComponentState rule marks (List.ofFn word)).sourceSelected then
        (rule.network.endpoint (word (Fin.last (depth + 1))).1).1
      else (rule.network.endpoint (word (Fin.last (depth + 1))).1).2) := by
    change (rule.network.openGraph _).Reachable (plantedVertex rule.network _) _
    rw [configuration_identity]
    exact child_reachable
  have inherited := (retainedOldVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent depth ⟨_, componentWordAnchor_retained rule marks crossing depth (Fin.init word) parent_live⟩).property
  have anchor_retained : ((rule.generation (depth + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (depth + 1) [] true)).Reachable
        (rule.generation (depth + 1)).network.source
        ((generationBlockCellEmbedding rule depth 0
          (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex
          (plantedVertex rule.network (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected)) := by
    rw [componentWordAnchor_block_parent]
    exact inherited
  have vertex_retained := componentWordAnchor_retained rule marks crossing (depth + 1) word live
  rw [componentWordAnchor_bottom] at vertex_retained
  have estimate := actualChemicalVertex_dist_block_le rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scale_positive
    limit_length nonnegative positive child_convergence depth 0
    (generationWordEdge rule depth (fun index => (Fin.init word index).1))
    (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected _ reachable
    anchor_retained vertex_retained bound microscopic_bound
  rw [actualComponentWordPoint, dif_pos parent_live, actualComponentWordPoint, dif_pos live,
    actualChemicalVertex_old]
  convert estimate using 1
  congr 2
  · apply Subtype.ext
    exact (componentWordAnchor_block_parent rule marks depth word).symm
  · apply Subtype.ext
    exact componentWordAnchor_bottom rule marks depth word

/-- The actual component boundary has a measurable realization in the
actual chemical completion. Its finite cylinder representatives converge
in Prokhorov distance to the resulting probability measure. -/
theorem exists_actual_component_boundary_pushforward
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    [IsProbabilityMeasure boundary]
    (retained_paths : ∀ᵐ path ∂boundary, ∀ depth,
      Fin.init (path (depth + 1)) = path depth ∧
      retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive)
    (eta coefficient : ℝ) (eta_nonnegative : 0 ≤ eta) (eta_lt_one : eta < 1)
    (coefficient_nonnegative : 0 ≤ coefficient) (start : ℕ)
    (microscopic_mesh : ∀ coarse fine (edge : Fin (rule.generation coarse).edges) side
      (vertex : Fin (rule.generation fine).vertices), start ≤ coarse →
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      (((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
          ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
          ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) : ℝ) /
          scale ^ (coarse + fine + 2) ≤ coefficient * eta ^ (coarse + 1)) :
    ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scale_positive limit_length nonnegative positive child_convergence,
      Measurable realization ∧ IsProbabilityMeasure (boundary.map realization) ∧
      (∀ᵐ path ∂boundary, Tendsto (fun depth => actualComponentWordPoint rule classicalRule marks crossing
        coherent scale scale_positive limit_length nonnegative positive child_convergence depth (path (depth + 1)))
          atTop (𝓝 (realization path))) ∧
      (∀ depth, ∀ᵐ path ∂boundary, dist
        (actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive limit_length
          nonnegative positive child_convergence (depth + start) (path (depth + start + 1)))
        (realization path) ≤ coefficient * eta ^ (start + 1) * eta ^ depth / (1 - eta)) ∧
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive
          limit_length nonnegative positive child_convergence depth (path (depth + 1))))
        (boundary.map realization)) atTop (𝓝 0) := by
  apply exists_measurable_geometric_boundary_limit boundary
    (fun depth path => actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive
      limit_length nonnegative positive child_convergence depth (path (depth + 1)))
    (fun depth => (measurable_of_finite (actualComponentWordPoint rule classicalRule marks crossing coherent
      scale scale_positive limit_length nonnegative positive child_convergence depth)).comp
        (measurable_pi_apply (depth + 1)))
    eta (coefficient * eta ^ (start + 1)) eta_nonnegative eta_lt_one
    (mul_nonneg coefficient_nonnegative (pow_nonneg eta_nonnegative _)) start
  filter_upwards [retained_paths] with path retained
  intro depth
  have parent_live : retainedComponentState rule marks
      (List.ofFn (Fin.init (path (depth + start + 2)))) ≠ .inactive := by
    rw [(retained (depth + start + 1)).1]
    exact (retained (depth + start + 1)).2
  have estimate := actualComponentWordPoint_successor_distance rule classicalRule marks crossing coherent
    scale scale_positive limit_length nonnegative positive child_convergence (depth + start)
    (path (depth + start + 2)) parent_live (retained (depth + start + 2)).2
    (coefficient * eta ^ (depth + start + 1)) (fun host point reachable =>
      microscopic_mesh (depth + start) host _ _ point (by omega) reachable)
  simpa only [(retained (depth + start + 1)).1, Nat.add_assoc, Nat.add_comm depth start,
    pow_add, mul_assoc, mul_comm, mul_left_comm] using estimate

end
end IGSIII.Geometry
