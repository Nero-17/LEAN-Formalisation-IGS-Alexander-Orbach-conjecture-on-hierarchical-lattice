import IGSIII34.Diffusion.ElectricalWordMeshCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

/-- Both half-edge masses are close to their exact original component-word
anchor in the actual electrical carrier, including noncrossing components. -/
theorem actualElectrical_halfowner_mesh_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (fine age : ℕ) (beyond : start ≤ age + 1)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool))
    (edge : ClusterEdge (rule.generation (fine + (age + 1))).network
      (stationaryConfiguration rule marks.val (fine + (age + 1)))) (side : Bool) :
    dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1))
      (halfEndpoint (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (fine + (age + 1)))
        (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _) (edge, side)))
      (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property age
        (actualComponentEdgeOwnership rule marks.val marks.property.2.1 fine (age + 1) fallback edge)) ≤ coefficient * eta ^ (age + 1) := by
  classical
  obtain ⟨child, childIdentity⟩ := finiteComponentOwnership_inside
    (Child := fun word : Fin (age + 1) → (Fin rule.edges × Bool) => SelectedComponentEdge rule marks.val fine
      ([] ++ componentEdgeAddress (List.ofFn word)) (retainedComponentStateFrom rule marks.val [] .connected (List.ofFn word)))
    (actualComponentEdgeEmbedding rule marks.val marks.property.2.1 fine (age + 1)) fallback edge
    (by rw [actualComponentEdgeFrontier_empty]; simp)
  let word := actualComponentEdgeOwnership rule marks.val marks.property.2.1 fine (age + 1) fallback edge
  have live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive := selectedComponentEdge_live rule marks.val fine _ _ child
  have selected := ((rule.generation fine).network.orientedChildState_connected_iff _ _ _ _).mp child.property
  change markedGenerationConfiguration rule marks.val fine (componentEdgeAddress (List.ofFn word))
      (retainedComponentState rule marks.val (List.ofFn word)).massOpened child.val = true ∧
    (rule.generation fine).network.selectedActive
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
      (retainedComponentState rule marks.val (List.ofFn word)).targetSelected
      (markedGenerationConfiguration rule marks.val fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks.val (List.ofFn word)).massOpened)
      ((rule.generation fine).network.endpoint child.val).1 = true at selected
  have bothSelected (side : Bool) : (rule.generation fine).network.selectedActive
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
      (retainedComponentState rule marks.val (List.ofFn word)).targetSelected
      (markedGenerationConfiguration rule marks.val fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks.val (List.ofFn word)).massOpened)
      (if side then ((rule.generation fine).network.endpoint child.val).1 else ((rule.generation fine).network.endpoint child.val).2) = true := by
    cases side
    · exact ((rule.generation fine).network.selectedActive_endpoints_eq_of_open _ _ _ child.val selected.1).symm.trans selected.2
    · exact selected.2
  let childVertex := if side then ((rule.generation fine).network.endpoint child.val).1 else ((rule.generation fine).network.endpoint child.val).2
  have reachable := (marked_component_selected_iff rule marks.val marks.property.2.1 fine (List.ofFn word) live _).mp (bothSelected side)
  have rawIdentity := congrArg (fun edge : ClusterEdge (rule.generation (fine + (age + 1))).network
    (markedGenerationConfiguration rule marks.val (fine + (age + 1)) [] true) => edge.val) childIdentity
  change (selectedComponentWordEdgeEmbedding rule marks.val marks.property.2.1 fine (age + 1) [] .connected ⟨word, child⟩).val = edge.val at rawIdentity
  rw [selectedComponentWordEdgeEmbedding_edge] at rawIdentity
  have endpointIdentity := (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).endpoint child.val
  rw [rawIdentity] at endpointIdentity
  let half := halfEndpoint (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive
    (fine + (age + 1))) (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _) (edge, side)
  have halfIdentity : half.val = (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex childVertex := by
    cases side
    · exact congrArg Prod.snd endpointIdentity
    · exact congrArg Prod.fst endpointIdentity
  have childRetained : ((rule.generation (fine + (age + 1))).network.openGraph
      (stationaryConfiguration rule marks.val (fine + (age + 1)))).Reachable (rule.generation (fine + (age + 1))).network.source
      ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex childVertex) :=
    halfIdentity ▸ half.property
  have estimate := actualElectrical_word_mesh_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks fieldLimit eta coefficient start radiusBound fine age beyond word live childVertex reachable childRetained
  have pointIdentity : (⟨(generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex childVertex,
      childRetained⟩ : RetainedSkeletonVertex (rule.generation (fine + (age + 1))).network
        (stationaryConfiguration rule marks.val (fine + (age + 1)))) = half := Subtype.ext halfIdentity.symm
  rw [pointIdentity, dist_comm] at estimate
  exact estimate

end
end IGSIII34.Diffusion
