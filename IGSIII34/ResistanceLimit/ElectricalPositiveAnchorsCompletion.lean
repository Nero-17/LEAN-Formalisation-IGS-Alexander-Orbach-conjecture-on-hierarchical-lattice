import IGSIII34.ResistanceLimit.ElectricalBoundaryCompletion
import IGSIII.Geometry.PositiveCylinderAnchors

set_option autoImplicit false
set_option maxHeartbeats 2200000
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

theorem actualElectrical_connected_cylinder_anchor_near_vertex
    (mesh : ℕ → ℝ) (meshNonnegative : ∀ depth, 0 ≤ mesh depth) (start coarse : ℕ)
    (beyond : start ≤ coarse)
    (edgeMesh : ∀ depth, start ≤ depth → ∀ edge,
      stationaryResistance rule p positive belowOne fixedPoint growth value marks depth edge ≤ mesh depth)
    (vertex : RetainedSkeletonVertex (rule.generation coarse).network (stationaryConfiguration rule marks coarse)) :
    ∃ word : Fin (coarse + 1) → (Fin rule.edges × Bool),
      retainedComponentState rule marks (List.ofFn word) = .connected ∧
      dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks, typical⟩ coarse vertex)
        (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
          marks typical coarse word) ≤ mesh coarse := by
  obtain ⟨edge, opened, firstRetained, lastRetained, incident⟩ := retained_vertex_incident_open_edge
    (rule.generation coarse).network _
    (markedGenerationConfiguration_crosses rule marks typical.2.1 coarse [] true) vertex.val vertex.property
  have connected : (rule.generation coarse).network.orientedChildState true true
      (stationaryConfiguration rule marks coarse) edge = .connected := by
    apply ((rule.generation coarse).network.orientedChildState_connected_iff _ _ _ _).mpr
    refine ⟨opened, ?_⟩
    simp only [selectedActive, Bool.true_and, Bool.or_eq_true, SimpleGraph.reachableDecide_eq_true]
    exact Or.inl firstRetained
  obtain ⟨word, edgeIdentity, stateIdentity⟩ := exists_connected_component_word rule marks typical.2.1
    coarse [] .connected edge connected
  change retainedComponentState rule marks (List.ofFn word) = .connected at stateIdentity
  have wordLive : retainedComponentState rule marks (List.ofFn word) ≠ .inactive := by rw [stateIdentity]; decide
  have pointIdentity : actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
      marks typical coarse word =
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks, typical⟩ coarse ⟨_, firstRetained⟩ := by
    rw [actualElectricalComponentWordPoint, dif_pos wordLive]
    congr 1
    apply Subtype.ext
    simp only [componentWordAnchor, stateIdentity, OrientedState.sourceSelected, ↓reduceIte, edgeIdentity]
  have edgeDistance : dist
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks, typical⟩ coarse ⟨_, firstRetained⟩)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks, typical⟩ coarse ⟨_, lastRetained⟩) ≤ mesh coarse := by
    rw [actualStationaryElectricalVertex_distance]
    exact (pairResistance_endpoint_le_edge_resistance
      (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks coarse)
      (fun edge => (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks, typical⟩ coarse edge).le) ⟨edge, opened⟩).trans (edgeMesh coarse beyond ⟨edge, opened⟩)
  refine ⟨word, stateIdentity, ?_⟩
  rw [pointIdentity]
  rcases incident with firstIdentity | lastIdentity
  · have identity : vertex = ⟨_, firstRetained⟩ := Subtype.ext firstIdentity
    rw [identity, dist_self]
    exact meshNonnegative coarse
  · have identity : vertex = ⟨_, lastRetained⟩ := Subtype.ext lastIdentity
    rw [identity, dist_comm]
    exact edgeDistance

theorem actualElectrical_connected_cylinder_anchors_dense
    (mesh : ℕ → ℝ) (meshNonnegative : ∀ depth, 0 ≤ mesh depth)
    (vanishing : Tendsto mesh atTop (𝓝 0)) (start : ℕ)
    (edgeMesh : ∀ depth, start ≤ depth → ∀ edge,
      stationaryResistance rule p positive belowOne fixedPoint growth value marks depth edge ≤ mesh depth) :
    ∀ point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩,
    ∀ radius : ℝ, 0 < radius → ∀ minimum : ℕ,
      ∃ depth, minimum ≤ depth ∧ ∃ word : Fin (depth + 1) → (Fin rule.edges × Bool),
        retainedComponentState rule marks (List.ofFn word) = .connected ∧
        dist point (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
          marks typical depth word) < radius := by
  intro point radius radiusPositive minimum
  obtain ⟨nearby, belongs, nearbyClose⟩ := (actualStationaryElectricalVertex_dense rule p positive belowOne
    fixedPoint growth value growthPositive ⟨marks, typical⟩).exists_dist_lt point (show 0 < radius / 2 by linarith)
  obtain ⟨birth, vertex, rfl⟩ := Set.mem_iUnion.mp belongs
  have meshSmall := (tendsto_order.mp vanishing).2 (radius / 2) (by linarith)
  obtain ⟨depth, meshSmall, beyondBirth, beyondStart, beyondMinimum⟩ :=
    (meshSmall.and ((eventually_ge_atTop birth).and ((eventually_ge_atTop start).and
      (eventually_ge_atTop minimum)))).exists
  obtain ⟨word, wordConnected, wordClose⟩ := actualElectrical_connected_cylinder_anchor_near_vertex
    rule p positive belowOne fixedPoint growth value growthPositive marks typical mesh meshNonnegative start depth beyondStart
    edgeMesh (retainedPersistentVertexEmbedding rule (stationaryConfiguration rule marks)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩) birth depth beyondBirth vertex)
  change dist (electricalVertex _ _ _ _ _ _ depth _) _ ≤ _ at wordClose
  rw [← electricalVertex_persistent rule (stationaryConfiguration rule marks)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩)
    typical.2.2 birth depth beyondBirth vertex] at wordClose
  refine ⟨depth, beyondMinimum, word, wordConnected, ?_⟩
  change dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks, typical⟩ birth vertex)
    (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
      marks typical depth word) ≤ mesh depth at wordClose
  exact (dist_triangle point
    (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks, typical⟩ birth vertex)
    (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks typical depth word)).trans_lt
      (by linarith)

end
end IGSIII34.ResistanceLimit
