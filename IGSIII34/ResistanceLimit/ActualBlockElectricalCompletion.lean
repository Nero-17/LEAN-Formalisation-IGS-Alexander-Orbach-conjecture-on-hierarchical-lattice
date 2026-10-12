import IGSIII34.ResistanceLimit.ElectricalPersistence
import IGSIII.Geometry.ActualBlockComponentLimits

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem pairResistance_endpoint_le_edge_resistance
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (nonnegative : ∀ edge, 0 ≤ resistance edge) (edge : Edge) :
    pairResistance network resistance (network.endpoint edge).1 (network.endpoint edge).2 ≤ resistance edge := by
  by_cases distinct : (network.endpoint edge).1 ≠ (network.endpoint edge).2
  · rw [pairResistance, dif_pos distinct]
    have singleFlow : (retarget network (network.endpoint edge).1 (network.endpoint edge).2 distinct).unitFlows
        (fun index => if index = edge then 1 else 0) := by
      intro vertex
      rw [Resistance.FiniteNetwork.divergence_single]
      simp only [retarget, one_mul, eq_comm]
    have below := (retarget network (network.endpoint edge).1 (network.endpoint edge).2 distinct).effectiveResistance_le_energy
      nonnegative singleFlow
    simpa only [Resistance.FiniteNetwork.energy, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using below
  · rw [not_ne_iff] at distinct
    rw [distinct, pairResistance_self]
    exact nonnegative edge

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})

theorem actualElectricalVertex_dist_block_le
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
        (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (coarse fine : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (vertex : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).Reachable
        (plantedVertex (rule.generation fine).network sourceSide) vertex)
    (anchorRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (stationaryConfiguration rule marks.val (coarse + fine + 1))).Reachable
        (rule.generation (coarse + fine + 1)).network.source
        ((generationBlockCellEmbedding rule coarse fine edge).vertex
          (plantedVertex (rule.generation fine).network sourceSide)))
    (vertexRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (stationaryConfiguration rule marks.val (coarse + fine + 1))).Reachable
        (rule.generation (coarse + fine + 1)).network.source
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex))
    (bound : ℝ)
    (microscopicBound : ∀ host (point : Fin (rule.generation host).vertices),
      ((rule.generation host).network.openGraph
        (generationBlockCells rule coarse host (stationaryConfiguration rule marks.val (coarse + host + 1)) edge)).Reachable
          (plantedVertex (rule.generation host).network sourceSide) point →
      pairResistance (network (rule.generation (coarse + host + 1)).network
          (stationaryConfiguration rule marks.val (coarse + host + 1))) (fun _ => 1)
        ((generationBlockCellEmbedding rule coarse host edge).vertex
          (plantedVertex (rule.generation host).network sourceSide))
        ((generationBlockCellEmbedding rule coarse host edge).vertex point) /
          growth ^ (coarse + host + 2) ≤ bound) :
    dist
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks
        (coarse + fine + 1) ⟨_, anchorRetained⟩)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks
        (coarse + fine + 1) ⟨_, vertexRetained⟩) ≤ bound := by
  rw [actualStationaryElectricalVertex_distance]
  have convergence := (actual_persistent_skeleton_resistances_tendsto rule marks.val marks.property.2.1
    growth growthPositive (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fun address => (marks.property.1 address).le) fieldLimit (coarse + fine + 1)
    (anchorRetained.symm.trans vertexRetained)).comp (tendsto_add_atTop_nat (coarse + 1))
  apply le_of_tendsto convergence
  filter_upwards [eventually_ge_atTop fine] with host beyond
  have childReachable := (persistentVertexEmbedding_reachable_iff rule
    (fun depth => generationBlockCells rule coarse depth (stationaryConfiguration rule marks.val (coarse + depth + 1)) edge)
    (generationBlockCells_sequence_coherent rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks) coarse edge)
    fine host beyond (plantedVertex (rule.generation fine).network sourceSide) vertex).mpr reachable
  rw [persistentVertexEmbedding_planted] at childReachable
  have estimate := microscopicBound host (persistentVertexEmbedding rule fine host beyond vertex) childReachable
  dsimp only [Function.comp_apply]
  rw [show host + (coarse + 1) = coarse + host + 1 by omega]
  simp only [persistentNormalizedResistance, dif_pos (show coarse + fine + 1 ≤ coarse + host + 1 by omega)]
  rw [generationBlockCellEmbedding_persistent rule coarse fine host beyond edge _,
    generationBlockCellEmbedding_persistent rule coarse fine host beyond edge _,
    persistentVertexEmbedding_planted]
  simpa only [Nat.add_assoc] using estimate

end
end IGSIII34.ResistanceLimit
