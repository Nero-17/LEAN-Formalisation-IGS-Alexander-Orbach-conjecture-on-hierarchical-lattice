import IGSIII34.ResistanceLimit.RetainedWordEnergy
import IGSIII34.ResistanceLimit.SideSourceTrace
import IGSIII.Geometry.ActualComponentSelection

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

theorem sideNetwork_endpoint {Vertex Edge : Type*}
    (network : Resistance.FiniteNetwork Vertex Edge) (sourceSide : Bool) :
    (sideNetwork network sourceSide).endpoint = network.endpoint := by
  cases sourceSide <;> rfl

theorem sideNetwork_network_source {vertices edges : ℕ}
    (original : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges) (sourceSide : Bool) :
    (sideNetwork (network original configuration) sourceSide).source = plantedVertex original sourceSide := by
  cases sourceSide <;> rfl

theorem pairResistance_sideNetwork {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (sourceSide : Bool)
    (resistance : Edge → ℝ) (first last : Vertex) :
    pairResistance (sideNetwork network sourceSide) resistance first last = pairResistance network resistance first last := by
  cases sourceSide <;> rfl

def selectedComponentTraceEnergy (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine : ℕ) (word : List (Fin rule.edges × Bool))
    (resistance : {edge : Fin (rule.generation fine).edges // markedGenerationConfiguration rule marks fine
      (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened edge = true} → ℝ)
    (potential : Fin (rule.generation fine).vertices → ℝ) : ℝ :=
  if retainedComponentState rule marks word = .inactive then 0 else
    sourceComponentEnergy (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word).massOpened))
      (retainedComponentState rule marks word).sourceSelected) resistance potential

theorem selectedComponentTraceEnergy_eq_sum
    (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine : ℕ) (word : List (Fin rule.edges × Bool))
    (resistance : {edge : Fin (rule.generation fine).edges // markedGenerationConfiguration rule marks fine
      (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened edge = true} → ℝ)
    (potential : Fin (rule.generation fine).vertices → ℝ) :
    selectedComponentTraceEnergy rule marks fine word resistance potential =
      ∑ edge : SelectedComponentEdge rule marks fine (componentEdgeAddress word)
          (retainedComponentState rule marks word),
        (resistance ⟨edge.val, ((rule.generation fine).network.orientedChildState_connected_iff _ _ _ _).mp edge.property |>.1⟩)⁻¹ *
          (potential ((rule.generation fine).network.endpoint edge.val).1 -
            potential ((rule.generation fine).network.endpoint edge.val).2) ^ 2 := by
  classical
  by_cases inactive : retainedComponentState rule marks word = .inactive
  · rw [selectedComponentTraceEnergy, if_pos inactive]
    haveI : IsEmpty (SelectedComponentEdge rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word)) := ⟨fun edge =>
      selectedComponentEdge_live rule marks fine (componentEdgeAddress word) _ edge inactive⟩
    simp
  · rw [selectedComponentTraceEnergy, if_neg inactive]
    let equivalence : SelectedComponentEdge rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word) ≃
        {edge : {edge : Fin (rule.generation fine).edges // markedGenerationConfiguration rule marks fine
          (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened edge = true} //
          ((rule.generation fine).network.openGraph (markedGenerationConfiguration rule marks fine
            (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened)).Reachable
              (plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected)
              ((rule.generation fine).network.endpoint edge.val).1} := {
      toFun := fun edge => ⟨⟨edge.val,
        (((rule.generation fine).network.orientedChildState_connected_iff _ _ _ _).mp edge.property).1⟩,
        (marked_component_selected_iff rule marks crossing fine word inactive _).mp
          (((rule.generation fine).network.orientedChildState_connected_iff _ _ _ _).mp edge.property).2⟩
      invFun := fun edge => ⟨edge.val.val,
        ((rule.generation fine).network.orientedChildState_connected_iff _ _ _ _).mpr
          ⟨edge.val.property, (marked_component_selected_iff rule marks crossing fine word inactive _).mpr edge.property⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
    let response := fun edge : {edge : Fin (rule.generation fine).edges // markedGenerationConfiguration rule marks fine
        (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened edge = true} =>
      (resistance edge)⁻¹ * (potential ((rule.generation fine).network.endpoint edge.val).1 -
        potential ((rule.generation fine).network.endpoint edge.val).2) ^ 2
    unfold sourceComponentEnergy finiteEnergy
    rw [sideNetwork_graph, graph_eq_openGraph]
    have sourceIdentity : (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
          (retainedComponentState rule marks word).massOpened))
        (retainedComponentState rule marks word).sourceSelected).source =
        plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected := by
      cases selected : (retainedComponentState rule marks word).sourceSelected <;> rfl
    rw [sourceIdentity]
    simp only [sideNetwork_endpoint, network, ite_mul, zero_mul]
    change (∑ edge, if ((rule.generation fine).network.openGraph
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word).massOpened)).Reachable
        (plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected)
        ((rule.generation fine).network.endpoint edge.val).1 then response edge else 0) = _
    have filtered :
        (∑ edge, if ((rule.generation fine).network.openGraph
          (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
            (retainedComponentState rule marks word).massOpened)).Reachable
            (plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected)
            ((rule.generation fine).network.endpoint edge.val).1 then response edge else 0) =
        ∑ edge : {edge : {edge : Fin (rule.generation fine).edges // markedGenerationConfiguration rule marks fine
          (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened edge = true} //
          ((rule.generation fine).network.openGraph (markedGenerationConfiguration rule marks fine
            (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened)).Reachable
              (plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected)
              ((rule.generation fine).network.endpoint edge.val).1}, response edge.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter fun edge : {edge : Fin (rule.generation fine).edges // markedGenerationConfiguration rule marks fine
          (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened edge = true} =>
          ((rule.generation fine).network.openGraph (markedGenerationConfiguration rule marks fine
            (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened)).Reachable
              (plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected)
              ((rule.generation fine).network.endpoint edge.val).1) (by simp) response
    rw [filtered]
    rw [← equivalence.sum_comp]
    rfl

theorem selectedComponentTraceEnergy_resistance_bound
    (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine : ℕ) (word : List (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks word ≠ .inactive)
    (resistance : {edge : Fin (rule.generation fine).edges // markedGenerationConfiguration rule marks fine
      (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : Fin (rule.generation fine).vertices → ℝ)
    (first last : Fin (rule.generation fine).vertices)
    (firstRetained : ((rule.generation fine).network.openGraph (markedGenerationConfiguration rule marks fine
      (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened)).Reachable
        (plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected) first)
    (lastRetained : ((rule.generation fine).network.openGraph (markedGenerationConfiguration rule marks fine
      (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened)).Reachable
        (plantedVertex (rule.generation fine).network (retainedComponentState rule marks word).sourceSelected) last) :
    (potential first - potential last) ^ 2 ≤
      pairResistance (network (rule.generation fine).network (markedGenerationConfiguration rule marks fine
        (componentEdgeAddress word) (retainedComponentState rule marks word).massOpened)) resistance first last *
      selectedComponentTraceEnergy rule marks fine word resistance potential := by
  rw [selectedComponentTraceEnergy, if_neg live]
  have firstSide : (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word).massOpened))
      (retainedComponentState rule marks word).sourceSelected).graph.Reachable
      (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word).massOpened))
      (retainedComponentState rule marks word).sourceSelected).source first := by
    rw [sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source]
    exact firstRetained
  have lastSide : (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word).massOpened))
      (retainedComponentState rule marks word).sourceSelected).graph.Reachable
      (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress word)
        (retainedComponentState rule marks word).massOpened))
      (retainedComponentState rule marks word).sourceSelected).source last := by
    rw [sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source]
    exact lastRetained
  simpa only [pairResistance_sideNetwork] using
    sourceComponentEnergy_resistance_bound _ resistance positive potential firstSide lastSide

end
end IGSIII34.ResistanceLimit
