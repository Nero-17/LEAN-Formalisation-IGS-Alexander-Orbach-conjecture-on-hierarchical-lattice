import IGSIII34.Diffusion.ExactEdgeOwnership
import IGSIII34.Diffusion.EdgeEmpiricalLaw
import IGSIII34.Diffusion.ActualDegreeMeasure
import IGSIII.Geometry.ActualComponentOwnershipMetric

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

instance clusterHalfMeasurableSpace {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : MeasurableSpace (ClusterEdge network configuration × Bool) := ⊤

theorem half_owner_map_singleton {Edge Component : Type*} [Fintype Edge] [Nonempty Edge]
    [Fintype Component] [DecidableEq Component]
    [MeasurableSpace (Edge × Bool)] [MeasurableSingletonClass (Edge × Bool)]
    [MeasurableSpace Component] [MeasurableSingletonClass Component]
    (owner : Edge → Component) (component : Component) :
    (halfMeasure (Edge := Edge)).map (fun half => owner half.1) {component} =
      ENNReal.ofReal (((Finset.univ.filter fun edge => owner edge = component).card : ℝ) / Fintype.card Edge) := by
  classical
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton component)]
  unfold halfMeasure
  rw [PMF.toMeasure_apply_fintype]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, finiteWeightPMF_apply]
  rw [← half_owner_weight owner component, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro half _
    split_ifs <;> simp
  · intro half _
    split_ifs
    · exact halfWeight_nonnegative half
    · exact le_rfl

theorem actual_half_owner_law (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    letI := clusterEdge_nonempty (rule.generation (fine + age)).network _
      (markedGenerationConfiguration_crosses rule marks crossing (fine + age) [] true)
    (halfMeasure (Edge := ClusterEdge (rule.generation (fine + age)).network
      (markedGenerationConfiguration rule marks (fine + age) [] true))).map
        (fun half => actualComponentEdgeOwnership rule marks crossing fine age fallback half.1) =
      edgeComponentWordLaw rule marks crossing fine age := by
  classical
  letI := clusterEdge_nonempty (rule.generation (fine + age)).network _
    (markedGenerationConfiguration_crosses rule marks crossing (fine + age) [] true)
  apply Measure.ext_of_singleton
  intro word
  rw [half_owner_map_singleton, actualComponentEdgeOwnership_fiber_card,
    edgeComponentWordLaw, finiteWeightPMF_singleton]
  congr 1
  rw [clusterEdge_card]
  have root := orientedEdgeReward_connected (rule.generation (fine + age)).network _
    (markedGenerationConfiguration_crosses rule marks crossing (fine + age) [] true)
  simpa only [edgeComponentWordWeight, markedComponentEdgeMass, markedOrientedEdgeMass,
    componentEdgeAddress, List.map_nil, retainedComponentState, retainedComponentStateFrom,
    OrientedState.massOpened, decide_true] using
    congrArg (fun count : ℝ => markedComponentEdgeMass rule marks fine (List.ofFn word) / count) root.symm

theorem actualComponentEdgeOwnership_half_distance_le
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool))
    (edge : ClusterEdge (rule.generation (fine + (age + 1))).network
      (markedGenerationConfiguration rule marks (fine + (age + 1)) [] true)) (side : Bool) :
    dist (halfEndpoint (Vertex := ActualFiniteCluster rule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + (age + 1)))
      (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _) (edge, side))
      (retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive age (fine + (age + 1)) (by omega)
        (actualComponentRetainedAnchor rule marks crossing age
          (actualComponentEdgeOwnership rule marks crossing fine (age + 1) fallback edge))) ≤
      (markedTerminalComponentRadius rule marks fine
        (componentEdgeAddress (List.ofFn (actualComponentEdgeOwnership rule marks crossing fine (age + 1) fallback edge)))
        (retainedComponentState rule marks (List.ofFn (actualComponentEdgeOwnership rule marks crossing fine (age + 1) fallback edge))).massOpened : ℝ) /
          scale ^ (fine + (age + 1) + 1) := by
  classical
  obtain ⟨child, childIdentity⟩ := finiteComponentOwnership_inside
    (Child := fun word : Fin (age + 1) → (Fin rule.edges × Bool) => SelectedComponentEdge rule marks fine
      ([] ++ componentEdgeAddress (List.ofFn word)) (retainedComponentStateFrom rule marks [] .connected (List.ofFn word)))
    (actualComponentEdgeEmbedding rule marks crossing fine (age + 1)) fallback edge
    (by rw [actualComponentEdgeFrontier_empty]; simp)
  let word := actualComponentEdgeOwnership rule marks crossing fine (age + 1) fallback edge
  have live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive :=
    selectedComponentEdge_live rule marks fine _ _ child
  have selected := ((rule.generation fine).network.orientedChildState_connected_iff _ _ _ _).mp child.property
  change markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
      (retainedComponentState rule marks (List.ofFn word)).massOpened child.val = true ∧
    (rule.generation fine).network.selectedActive
      (retainedComponentState rule marks (List.ofFn word)).sourceSelected
      (retainedComponentState rule marks (List.ofFn word)).targetSelected
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened)
      ((rule.generation fine).network.endpoint child.val).1 = true at selected
  have bothSelected (side : Bool) : (rule.generation fine).network.selectedActive
      (retainedComponentState rule marks (List.ofFn word)).sourceSelected
      (retainedComponentState rule marks (List.ofFn word)).targetSelected
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened)
      (if side then ((rule.generation fine).network.endpoint child.val).1 else
        ((rule.generation fine).network.endpoint child.val).2) = true := by
    cases side
    · exact ((rule.generation fine).network.selectedActive_endpoints_eq_of_open _ _ _ child.val selected.1).symm.trans selected.2
    · exact selected.2
  have reachable := (marked_component_selected_iff rule marks crossing fine (List.ofFn word) live _).mp (bothSelected side)
  have distanceBound := generationComponentWordEmbedding_distance_to_planted_le rule marks fine (age + 1) word live _ reachable
  have rawIdentity := congrArg (fun edge : ClusterEdge (rule.generation (fine + (age + 1))).network
    (markedGenerationConfiguration rule marks (fine + (age + 1)) [] true) => edge.val) childIdentity
  change (selectedComponentWordEdgeEmbedding rule marks crossing fine (age + 1) [] .connected ⟨word, child⟩).val = edge.val at rawIdentity
  rw [selectedComponentWordEdgeEmbedding_edge] at rawIdentity
  have endpointIdentity := (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).endpoint child.val
  rw [rawIdentity] at endpointIdentity
  have halfIdentity : (if side then ((rule.generation (fine + (age + 1))).network.endpoint edge.val).1 else
      ((rule.generation (fine + (age + 1))).network.endpoint edge.val).2) =
      (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex
        (if side then ((rule.generation fine).network.endpoint child.val).1 else
          ((rule.generation fine).network.endpoint child.val).2) := by
    cases side
    · exact congrArg Prod.snd endpointIdentity
    · exact congrArg Prod.fst endpointIdentity
  have plantedIdentity := generationComponentWordEmbedding_planted rule fine age
    (fun index => (word index).1) (retainedComponentState rule marks (List.ofFn word)).sourceSelected
  change (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex
      (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn word)).sourceSelected) =
      persistentVertexEmbedding rule age (fine + age + 1) (by omega) (componentWordAnchor rule marks age word) at plantedIdentity
  have halfVal : (halfEndpoint (Vertex := ActualFiniteCluster rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + (age + 1)))
      (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _) (edge, side)).val =
      (if side then ((rule.generation (fine + (age + 1))).network.endpoint edge.val).1 else
        ((rule.generation (fine + (age + 1))).network.endpoint edge.val).2) := by
    cases side <;> rfl
  change (((rule.generation (fine + (age + 1))).network.openGraph
      (markedGenerationConfiguration rule marks (fine + (age + 1)) [] true)).dist
      (halfEndpoint (Vertex := ActualFiniteCluster rule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + (age + 1)))
        (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _) (edge, side)).val
      (persistentVertexEmbedding rule age (fine + (age + 1)) (by omega)
        (actualComponentRetainedAnchor rule marks crossing age word).val) : ℝ) /
          scale ^ (fine + (age + 1) + 1) ≤ _
  simp only [actualComponentRetainedAnchor, dif_pos live]
  rw [halfVal, halfIdentity, SimpleGraph.dist_comm]
  have normalized := div_le_div_of_nonneg_right (show
    (((rule.generation (fine + (age + 1))).network.openGraph
      (markedGenerationConfiguration rule marks (fine + (age + 1)) [] true)).dist
      ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex
        (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn word)).sourceSelected))
      ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex
        (if side then ((rule.generation fine).network.endpoint child.val).1 else
          ((rule.generation fine).network.endpoint child.val).2)) : ℝ) ≤
      markedTerminalComponentRadius rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened by exact_mod_cast distanceBound)
    (pow_pos scalePositive (fine + (age + 1) + 1)).le
  rw [plantedIdentity] at normalized
  exact normalized

end
end IGSIII34.Diffusion
