import IGSIII34.ResistanceLimit.SkeletonLimits
import IGSIII34.ResistanceLimit.ActualStationaryCompletion
import IGSIII34.Percolation.ElectricalAlmostSure

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open IGSIII.Probability
open scoped _root_.Topology

theorem actual_electrical_field_limits_fixed_cluster
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
      Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address)
        atTop (𝓝 (electricalField rule p positive belowOne fixedPoint endpoint address marks)) := by
  have rootConvergence := electricalOrbitLp_tendsto_ae_fixed_cluster rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership
  have rootLimit : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth [])
        atTop (𝓝 (endpoint marks)) := by
    filter_upwards [rootConvergence, ae_all_iff.mpr
      (electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le)] with marks limit identities
    simpa only [identities] using limit
  apply ae_all_iff.mpr
  intro address
  have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootLimit
  simpa only [electricalIteration_shift, List.append_nil, electricalField] using shifted

/-- The actual open block's rescaled terminal response converges to its
stationary electrical weight. Its original coarse state selects the child. -/
theorem actual_marked_block_resistance_limit (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (field : List (Fin rule.edges) → ℝ)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ)
    (edge : {edge : Fin (rule.generation coarse).edges // stationaryConfiguration rule marks coarse edge = true}) :
    Tendsto (fun fine => (growth ^ (coarse + fine + 2))⁻¹ *
      unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge.val))
      atTop (𝓝 (stationaryGenerationResistance rule field growth coarse [] edge.val)) := by
  have shifted := ((fieldLimit (generationEdgeAddress rule coarse edge.val)).comp
    (tendsto_add_atTop_nat 1)).const_mul (growth⁻¹ ^ (coarse + 1))
  apply shifted.congr'
  apply Eventually.of_forall
  intro fine
  dsimp only [Function.comp_def]
  have childIdentity := generationBlockCells_marked rule marks coarse fine [] true edge.val
  change generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge.val = _ at childIdentity
  rw [childIdentity]
  simp only [List.nil_append, show markedGenerationConfiguration rule marks coarse [] true edge.val = true from edge.property]
  rw [markedGeneration_resistance_eq_iteration rule marks crossing]
  simp only [inv_pow]
  rw [show coarse + fine + 2 = (coarse + 1) + (fine + 1) by omega]
  simp only [pow_add, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

theorem actual_marked_skeleton_resistances_tendsto (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldNonnegative : ∀ address, 0 ≤ field address)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ) {first last : Fin (rule.generation coarse).vertices}
    (reachable : ((rule.generation coarse).network.openGraph (stationaryConfiguration rule marks coarse)).Reachable first last) :
    Tendsto (fun fine => (growth ^ (coarse + fine + 2))⁻¹ *
      pairResistance (network (rule.generation (coarse + fine + 1)).network
        (stationaryConfiguration rule marks (coarse + fine + 1))) (fun _ => 1)
        (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last))
      atTop (𝓝 (pairResistance (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
        (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val) first last)) := by
  exact actual_block_skeleton_resistances_tendsto rule (stationaryConfiguration rule marks)
    (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth [] true)
    growth growthPositive coarse
    (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val)
    (fun edge => mul_nonneg (pow_nonneg (inv_nonneg.mpr growthPositive.le) _) (fieldNonnegative _))
    (actual_marked_block_resistance_limit rule marks crossing growth field fieldLimit coarse) reachable

end
end IGSIII34.ResistanceLimit
