import IGSIII34.Diffusion.OriginalValuesUniformCompletion
import IGSIII34.ResistanceLimit.ActualAvailableCellCoverCompletion
import IGSIII34.ResistanceLimit.ElectricalPersistence
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped BigOperators _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})


def originalRetainedOldValueCompletion
    (rule : Rule) (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (coarse : ℕ) (vertex : Fin (rule.generation coarse).vertices) (depth : ℕ) : ℝ :=
  if beyond : coarse ≤ depth then potentials depth (persistentVertexEmbedding rule coarse depth beyond vertex) else 0
/-- Bounded original energies and convergence on each persistent retained
vertex imply uniform convergence on all actual embedded finite vertices.
The proof combines original cell amplitudes with the independently proved
electrical distance mesh on the same anchors. -/
theorem originalPotential_selected_values_uniform_completion
    [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (limitPotential : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks, ℝ))
    (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (oldValuesConverge : ∀ coarse (vertex : RetainedSkeletonVertex (rule.generation coarse).network
      (stationaryConfiguration rule marks.val coarse)), Tendsto
      (fun index => originalRetainedOldValueCompletion rule potentials coarse vertex.val (selected index)) atTop
      (𝓝 (limitPotential (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))))
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (energyBound : ∀ depth, growth ^ (depth + 1) * sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) (fun _ => 1) (potentials depth) ≤ bound) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
        |potentials (selected index) vertex.val - limitPotential
          (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (selected index) vertex)| < tolerance := by
  classical
  intro tolerance tolerancePositive
  have thirdPositive : 0 < tolerance / 3 := by positivity
  obtain ⟨delta, deltaPositive, continuousClose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous limitPotential.continuous) (tolerance / 3) thirdPositive
  have meshZero : Tendsto (fun coarse : ℕ => coefficient * eta ^ (coarse + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp
      (tendsto_add_atTop_nat 1)).const_mul coefficient
  have amplitudeZero : Tendsto (fun coarse : ℕ => coefficient * eta ^ (coarse + 1) * bound) atTop (𝓝 (0 : ℝ)) :=
    by simpa only [zero_mul] using meshZero.mul_const bound
  have eventuallyMesh := meshZero.eventually (gt_mem_nhds deltaPositive)
  have eventuallyAmplitude := amplitudeZero.eventually (gt_mem_nhds (sq_pos_of_pos thirdPositive))
  obtain ⟨coarse, coarseBeyond, meshSmall, amplitudeSmall⟩ :=
    ((eventually_ge_atTop start).and (eventuallyMesh.and eventuallyAmplitude)).exists
  have anchorConvergence : ∀ vertex : RetainedSkeletonVertex (rule.generation coarse).network
      (stationaryConfiguration rule marks.val coarse), ∀ᶠ index in atTop,
      |originalRetainedOldValueCompletion rule potentials coarse vertex.val (selected index) -
        limitPotential (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex)| < tolerance / 3 := by
    intro vertex
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (oldValuesConverge coarse vertex).eventually (Metric.ball_mem_nhds _ thirdPositive)
  obtain ⟨indexStart, anchorClose⟩ := eventually_atTop.mp (eventually_all.mpr anchorConvergence)
  filter_upwards [eventually_ge_atTop indexStart, selectedAtTop.eventually (eventually_ge_atTop (coarse + 1))]
    with index indexBeyond depthBeyond
  obtain ⟨fine, depthIdentity⟩ : ∃ fine, selected index = coarse + fine + 1 :=
    ⟨selected index - coarse - 1, by omega⟩
  rw [depthIdentity]
  intro vertex
  obtain ⟨edge, child, side, vertexIdentity, reachable, anchorRetained⟩ :=
    actual_retained_generation_available_cell_cover rule marks.val marks.property.2.1 coarse fine vertex.val vertex.property
  have childRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (stationaryConfiguration rule marks.val (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex child) :=
    vertexIdentity ▸ vertex.property
  have mapped := reachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom
    (stationaryConfiguration rule marks.val (coarse + fine + 1)))
  have terminalRetained := childRetained.trans (by simpa only [generationBlockCellEmbedding_openGraphHom_apply] using mapped.symm)
  have amplitude := original_block_energy_oscillation_completion rule marks.val growth eta coefficient start growthPositive
    etaNonnegative coefficientNonnegative radiusBound coarse fine edge side child coarseBeyond reachable childRetained
    (potentials (coarse + fine + 1)) bound (by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using energyBound (coarse + fine + 1))
  have voltageClose : |potentials (coarse + fine + 1) vertex.val -
      potentials (coarse + fine + 1) ((generationBlockCellEmbedding rule coarse fine edge).vertex
        (plantedVertex (rule.generation fine).network side))| < tolerance / 3 := by
    rw [vertexIdentity]
    apply abs_lt.mpr
    constructor <;> nlinarith [amplitude.trans_lt amplitudeSmall]
  have distance := actualElectricalVertex_dist_block_le rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit coarse fine edge side child reachable terminalRetained childRetained (coefficient * eta ^ (coarse + 1))
    (fun host point pointReachable => original_block_normalized_resistance_bound_completion rule marks.val growth eta
      coefficient start growthPositive radiusBound coarse host edge side point coarseBeyond pointReachable)
  rw [actualElectrical_block_anchor_eq_coarse_completion rule p positive belowOne fixedPoint growth value
    growthPositive marks coarse fine edge side anchorRetained terminalRetained] at distance
  have childVertex : (⟨(generationBlockCellEmbedding rule coarse fine edge).vertex child, childRetained⟩ :
      RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks.val (coarse + fine + 1))) = vertex :=
    Subtype.ext vertexIdentity.symm
  rw [childVertex] at distance
  have limitClose := continuousClose (distance.trans_lt meshSmall)
  rw [Real.dist_eq] at limitClose
  have persistentAnchorClose := anchorClose index indexBeyond
    ⟨if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2, anchorRetained⟩
  rw [depthIdentity, originalRetainedOldValueCompletion, dif_pos (by omega : coarse ≤ coarse + fine + 1),
    ← blockOldVertexEmbedding_eq_persistent] at persistentAnchorClose
  have combine (a b c d : ℝ) (firstError : |a - b| < tolerance / 3)
      (secondError : |b - c| < tolerance / 3) (thirdError : |c - d| < tolerance / 3) :
      |a - d| < tolerance := by
    linarith [abs_sub_le a b d, abs_sub_le b c d]
  cases side <;> simp only [plantedVertex, Bool.false_eq_true, if_false, if_true,
    generationBlockCellEmbedding_source, generationBlockCellEmbedding_target] at voltageClose persistentAnchorClose limitClose
  all_goals exact combine _ _ _ _ voltageClose persistentAnchorClose limitClose

end
end IGSIII34.Diffusion
