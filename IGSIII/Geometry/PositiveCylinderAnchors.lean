import IGSIII.Geometry.ActualComponentBoundary
import IGSIII.Geometry.ConnectedComponentWords

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

theorem reachable_distinct_has_neighbor {Vertex : Type*} (graph : SimpleGraph Vertex)
    {first last : Vertex} (distinct : first ≠ last) (reachable : graph.Reachable first last) :
    ∃ neighbor, graph.Adj first neighbor := by
  obtain ⟨walk⟩ := reachable
  cases walk with
  | nil => exact (distinct rfl).elim
  | cons adjacent tail => exact ⟨_, adjacent⟩

/-- Every vertex of the actual crossing cluster meets an actual retained
open indexed edge, including the two planted terminals. -/
theorem retained_vertex_incident_open_edge {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crossing : network.crosses configuration = true) (vertex : Fin vertices)
    (retained : (network.openGraph configuration).Reachable network.source vertex) :
    ∃ edge : Fin edges, configuration edge = true ∧
      (network.openGraph configuration).Reachable network.source (network.endpoint edge).1 ∧
      (network.openGraph configuration).Reachable network.source (network.endpoint edge).2 ∧
      (vertex = (network.endpoint edge).1 ∨ vertex = (network.endpoint edge).2) := by
  have neighbor : ∃ neighbor, (network.openGraph configuration).Adj vertex neighbor := by
    by_cases at_source : vertex = network.source
    · subst vertex
      exact reachable_distinct_has_neighbor _ network.terminals_distinct ((network.crosses_eq_true _).mp crossing)
    · exact reachable_distinct_has_neighbor _ at_source retained.symm
  obtain ⟨neighbor, adjacent⟩ := neighbor
  have neighbor_retained := retained.trans adjacent.reachable
  obtain ⟨_, edge, opened, endpoints⟩ := adjacent
  refine ⟨edge, opened, ?_⟩
  rcases endpoints with endpoints | endpoints
  · rw [endpoints]
    exact ⟨retained, neighbor_retained, Or.inl rfl⟩
  · rw [endpoints]
    exact ⟨neighbor_retained, retained, Or.inr rfl⟩

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

theorem actualChemicalVertex_open_edge_distance_le (coarse : ℕ)
    (edge : Fin (rule.generation coarse).edges)
    (first_retained : ((rule.generation coarse).network.openGraph
      (markedGenerationConfiguration rule marks coarse [] true)).Reachable (rule.generation coarse).network.source
        ((rule.generation coarse).network.endpoint edge).1)
    (last_retained : ((rule.generation coarse).network.openGraph
      (markedGenerationConfiguration rule marks coarse [] true)).Reachable (rule.generation coarse).network.source
        ((rule.generation coarse).network.endpoint edge).2)
    (bound : ℝ)
    (microscopic_bound : ∀ fine,
      (((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
          ((generationBlockCellEmbedding rule coarse fine edge).vertex (rule.generation fine).network.source)
          ((generationBlockCellEmbedding rule coarse fine edge).vertex (rule.generation fine).network.target) : ℝ) /
          scale ^ (coarse + fine + 2) ≤ bound) :
    dist (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scale_positive limit_length nonnegative positive child_convergence coarse ⟨_, first_retained⟩)
      (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scale_positive limit_length nonnegative positive child_convergence coarse ⟨_, last_retained⟩) ≤ bound := by
  rw [actualChemicalVertex_distance]
  apply le_of_tendsto (actual_block_skeleton_distances_tendsto rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scale_positive coarse
    (limit_length coarse) (child_convergence coarse) (first_retained.symm.trans last_retained))
  apply Eventually.of_forall
  intro fine
  simpa only [generationBlockCellEmbedding_source, generationBlockCellEmbedding_target] using microscopic_bound fine

theorem actual_connected_cylinder_anchor_near_vertex
    (mesh : ℕ → ℝ) (mesh_nonnegative : ∀ depth, 0 ≤ mesh depth) (start coarse : ℕ)
    (beyond : start ≤ coarse)
    (microscopic_mesh : ∀ depth fine (edge : Fin (rule.generation depth).edges) side
      (vertex : Fin (rule.generation fine).vertices), start ≤ depth →
      ((rule.generation fine).network.openGraph (generationBlockCells rule depth fine
        (markedGenerationConfiguration rule marks (depth + fine + 1) [] true) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      (((rule.generation (depth + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (depth + fine + 1) [] true)).dist
          ((generationBlockCellEmbedding rule depth fine edge).vertex (plantedVertex (rule.generation fine).network side))
          ((generationBlockCellEmbedding rule depth fine edge).vertex vertex) : ℝ) /
          scale ^ (depth + fine + 2) ≤ mesh depth)
    (vertex : RetainedSkeletonVertex (rule.generation coarse).network
      (markedGenerationConfiguration rule marks coarse [] true)) :
    ∃ word : Fin (coarse + 1) → (Fin rule.edges × Bool),
      retainedComponentState rule marks (List.ofFn word) = .connected ∧
      dist (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scale_positive limit_length nonnegative positive child_convergence coarse vertex)
        (actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive limit_length
          nonnegative positive child_convergence coarse word) ≤ mesh coarse := by
  obtain ⟨edge, opened, first_retained, last_retained, incident⟩ := retained_vertex_incident_open_edge
    (rule.generation coarse).network _ (markedGenerationConfiguration_crosses rule marks crossing coarse [] true)
    vertex.val vertex.property
  have connected : (rule.generation coarse).network.orientedChildState true true
      (markedGenerationConfiguration rule marks coarse [] true) edge = .connected := by
    apply ((rule.generation coarse).network.orientedChildState_connected_iff _ _ _ _).mpr
    refine ⟨opened, ?_⟩
    simp only [selectedActive, Bool.true_and,
      Bool.or_eq_true, SimpleGraph.reachableDecide_eq_true]
    exact Or.inl first_retained
  obtain ⟨word, edge_identity, state_identity⟩ := exists_connected_component_word rule marks crossing coarse [] .connected edge connected
  change retainedComponentState rule marks (List.ofFn word) = .connected at state_identity
  have word_live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive := by rw [state_identity]; decide
  have point_identity : actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive limit_length
      nonnegative positive child_convergence coarse word =
      actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scale_positive limit_length nonnegative positive child_convergence coarse ⟨_, first_retained⟩ := by
    rw [actualComponentWordPoint, dif_pos word_live]
    congr 1
    apply Subtype.ext
    simp only [componentWordAnchor, state_identity, OrientedState.sourceSelected, ↓reduceIte, edge_identity]
  have edge_distance := actualChemicalVertex_open_edge_distance_le rule classicalRule marks coherent scale scale_positive
    limit_length nonnegative positive child_convergence coarse edge first_retained last_retained (mesh coarse) (fun fine => by
      have child_crossing : (rule.generation fine).network.crosses (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) = true := by
        change generationBlockCoarse rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge = true
        rw [generationBlockCoarse_of_coherent rule _ coherent]
        exact opened
      exact microscopic_mesh coarse fine edge true (rule.generation fine).network.target beyond
        (((rule.generation fine).network.crosses_eq_true _).mp child_crossing))
  refine ⟨word, state_identity, ?_⟩
  rw [point_identity]
  rcases incident with first_identity | last_identity
  · have identity : vertex = ⟨_, first_retained⟩ := Subtype.ext first_identity
    rw [identity, dist_self]
    exact mesh_nonnegative coarse
  · have identity : vertex = ⟨_, last_retained⟩ := Subtype.ext last_identity
    rw [identity, dist_comm]
    exact edge_distance

/-- Connected, hence positive-mass, cylinder anchors are dense at every
tail of the actual chemical skeleton tower. -/
theorem actual_connected_cylinder_anchors_dense
    (mesh : ℕ → ℝ) (mesh_nonnegative : ∀ depth, 0 ≤ mesh depth)
    (vanishing : Tendsto mesh atTop (𝓝 0)) (start : ℕ)
    (microscopic_mesh : ∀ depth fine (edge : Fin (rule.generation depth).edges) side
      (vertex : Fin (rule.generation fine).vertices), start ≤ depth →
      ((rule.generation fine).network.openGraph (generationBlockCells rule depth fine
        (markedGenerationConfiguration rule marks (depth + fine + 1) [] true) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      (((rule.generation (depth + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (depth + fine + 1) [] true)).dist
          ((generationBlockCellEmbedding rule depth fine edge).vertex (plantedVertex (rule.generation fine).network side))
          ((generationBlockCellEmbedding rule depth fine edge).vertex vertex) : ℝ) /
          scale ^ (depth + fine + 2) ≤ mesh depth) :
    ∀ point : ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scale_positive limit_length nonnegative positive child_convergence,
    ∀ radius : ℝ, 0 < radius → ∀ minimum : ℕ,
      ∃ depth, minimum ≤ depth ∧ ∃ word : Fin (depth + 1) → (Fin rule.edges × Bool),
        retainedComponentState rule marks (List.ofFn word) = .connected ∧
        dist point (actualComponentWordPoint rule classicalRule marks crossing coherent scale scale_positive limit_length
          nonnegative positive child_convergence depth word) < radius := by
  intro point radius radius_positive minimum
  obtain ⟨nearby, belongs, nearby_close⟩ := (actualChemicalVertex_dense rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scale_positive
    limit_length nonnegative positive child_convergence).exists_dist_lt point (show 0 < radius / 2 by linarith)
  obtain ⟨birth, vertex, rfl⟩ := Set.mem_iUnion.mp belongs
  have mesh_small := (tendsto_order.mp vanishing).2 (radius / 2) (by linarith)
  obtain ⟨depth, mesh_small, beyond_birth, beyond_start, beyond_minimum⟩ :=
    (mesh_small.and ((eventually_ge_atTop birth).and ((eventually_ge_atTop start).and (eventually_ge_atTop minimum)))).exists
  obtain ⟨word, word_connected, word_close⟩ := actual_connected_cylinder_anchor_near_vertex rule classicalRule marks crossing
    coherent scale scale_positive limit_length nonnegative positive child_convergence mesh mesh_nonnegative start depth beyond_start
    microscopic_mesh (retainedPersistentVertexEmbedding rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent birth depth beyond_birth vertex)
  rw [← actualChemicalVertex_persistent rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scale_positive
    limit_length nonnegative positive child_convergence birth depth beyond_birth vertex] at word_close
  refine ⟨depth, beyond_minimum, word, word_connected, ?_⟩
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end
end IGSIII.Geometry
