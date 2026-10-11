import IGSIII34.Diffusion.ActualDegreeProjection
import IGSIII34.ResistanceLimit.ElectricalBoundaryCompletion20261011
import IGSIII34.ResistanceLimit.RadiusMesh
import IGSIII34.ResistanceLimit.ActualRayleigh
import IGSIII34.ResistanceLimit.ElectricalNets

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})

/-- Every point of a real available component lies within the original
electrical radius mesh of its retained component-word anchor. -/
theorem actualElectrical_word_mesh_completion20261011
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (fine age : ℕ) (beyond : start ≤ age + 1) (word : Fin (age + 1) → (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)
    (vertex : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph
      (markedGenerationConfiguration rule marks.val fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks.val (List.ofFn word)).massOpened)).Reachable
      (plantedVertex (rule.generation fine).network (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected) vertex)
    (retained : ((rule.generation (fine + (age + 1))).network.openGraph
      (stationaryConfiguration rule marks.val (fine + (age + 1)))).Reachable
      (rule.generation (fine + (age + 1))).network.source
      ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex vertex)) :
    dist (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property age word)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1))
        ⟨_, retained⟩) ≤ coefficient * eta ^ (age + 1) := by
  let side := (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
  let embedded := generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)
  have localReachable : ((rule.generation fine).network.openGraph
      (embedded.restrict (stationaryConfiguration rule marks.val (fine + (age + 1))))).Reachable
      (plantedVertex (rule.generation fine).network side) vertex := by
    dsimp only [embedded, stationaryConfiguration]
    rw [generationComponentWordEmbedding_restrict rule marks.val fine (age + 1) word live]
    exact reachable
  have mapped := localReachable.map (embedded.openGraphHom (stationaryConfiguration rule marks.val (fine + (age + 1))))
  have anchorRetained : ((rule.generation (fine + (age + 1))).network.openGraph
      (stationaryConfiguration rule marks.val (fine + (age + 1)))).Reachable
      (rule.generation (fine + (age + 1))).network.source
      (embedded.vertex (plantedVertex (rule.generation fine).network side)) :=
    retained.trans mapped.symm
  have convergence := (actual_persistent_skeleton_resistances_tendsto rule marks.val marks.property.2.1 growth growthPositive
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fun address => (marks.property.1 address).le) fieldLimit (fine + (age + 1)) mapped).comp
    (tendsto_add_atTop_nat (age + 1))
  have distanceUpper : dist
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1))
        ⟨embedded.vertex (plantedVertex (rule.generation fine).network side), anchorRetained⟩)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1))
        ⟨_, retained⟩) ≤ coefficient * eta ^ (age + 1) := by
    rw [actualStationaryElectricalVertex_distance]
    apply le_of_tendsto convergence
    filter_upwards [eventually_ge_atTop fine] with host large
    have childReachable := (persistentVertexEmbedding_reachable_iff rule
      (fun depth => markedGenerationConfiguration rule marks.val depth (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks.val (List.ofFn word)).massOpened)
      (fun depth => markedGenerationConfiguration_coarsens rule marks.val marks.property.2.1 depth _ _) fine host large
      (plantedVertex (rule.generation fine).network side) vertex).mpr reachable
    rw [persistentVertexEmbedding_planted] at childReachable
    have restrictedReachable : ((rule.generation host).network.openGraph
        ((generationComponentWordEmbedding rule host (age + 1) (fun index => (word index).1)).restrict
          (stationaryConfiguration rule marks.val (host + (age + 1))))).Reachable
        (plantedVertex (rule.generation host).network side) (persistentVertexEmbedding rule fine host large vertex) := by
      dsimp only [stationaryConfiguration]
      rw [generationComponentWordEmbedding_restrict rule marks.val host (age + 1) word live]
      exact childReachable
    have original := networkEmbedding_unit_pairResistance_le
      (generationComponentWordEmbedding rule host (age + 1) (fun index => (word index).1))
      (stationaryConfiguration rule marks.val (host + (age + 1)))
      (plantedVertex (rule.generation host).network side) (persistentVertexEmbedding rule fine host large vertex) restrictedReachable
    have restrictedIdentity := generationComponentWordEmbedding_restrict rule marks.val host (age + 1) word live
    have responseIdentity := congrArg (fun configuration : Configuration (rule.generation host).edges =>
      pairResistance (network (rule.generation host).network configuration) (fun _ => 1)
        (plantedVertex (rule.generation host).network side) (persistentVertexEmbedding rule fine host large vertex)) restrictedIdentity
    have upper := (original.trans_eq responseIdentity).trans (planted_pairResistance_le_radius (rule.generation host).network
      (markedGenerationConfiguration rule marks.val host (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks.val (List.ofFn word)).massOpened) side _)
    have normalized := div_le_div_of_nonneg_right upper (pow_pos growthPositive (host + (age + 1) + 1)).le
    have mesh := radiusBound (componentEdgeAddress (List.ofFn word))
      (retainedComponentState rule marks.val (List.ofFn word)).massOpened host (by
        simpa only [componentEdgeAddress, List.length_map, List.length_ofFn] using beyond)
    dsimp only [Function.comp_def, persistentNormalizedResistance]
    rw [dif_pos (show fine + (age + 1) ≤ host + (age + 1) by omega)]
    dsimp only [embedded]
    change pairResistance (network (rule.generation (host + (age + 1))).network
      (stationaryConfiguration rule marks.val (host + (age + 1)))) (fun _ => 1)
      (persistentVertexEmbedding rule (fine + (age + 1)) (host + (age + 1)) (by omega)
        ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex
          (plantedVertex (rule.generation fine).network side)))
      (persistentVertexEmbedding rule (fine + (age + 1)) (host + (age + 1)) (by omega)
        ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex vertex)) /
      growth ^ (host + (age + 1) + 1) ≤ _
    rw [generationComponentWordEmbedding_persistent rule fine host large (age + 1) (fun index => (word index).1),
      generationComponentWordEmbedding_persistent rule fine host large (age + 1) (fun index => (word index).1),
      persistentVertexEmbedding_planted]
    exact normalized.trans (by
      simpa only [markedElectricalRadius, componentEdgeAddress, List.length_map, List.length_ofFn, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using mesh)
  have persistent := electricalVertex_persistent rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    marks.property.2.2 age (fine + (age + 1)) (by omega)
    ⟨componentWordAnchor rule marks.val age word, componentWordAnchor_retained rule marks.val marks.property.2.1 age word live⟩
  have anchorIdentity : actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property age word =
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1))
        ⟨embedded.vertex (plantedVertex (rule.generation fine).network side), anchorRetained⟩ := by
    rw [actualElectricalComponentWordPoint, dif_pos live]
    unfold actualStationaryElectricalVertex
    rw [persistent]
    apply congrArg (electricalVertex rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
      marks.property.2.2 (fine + (age + 1)))
    apply Subtype.ext
    rw [retainedPersistentVertexEmbedding_val]
    exact (generationComponentWordEmbedding_planted rule fine age (fun index => (word index).1) side).symm
  rw [anchorIdentity]
  exact distanceUpper

end
end IGSIII34.Diffusion
