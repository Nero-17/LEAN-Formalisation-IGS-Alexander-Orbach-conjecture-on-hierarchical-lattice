import IGSIII34.Diffusion.ActualBlockComponentResistance
import IGSIII34.Forms.BlockZeroEnergyScaling
import IGSIII34.ResistanceLimit.StationaryBlockBoundaryEnergy
import IGSIII34.ResistanceLimit.PairContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

def stationaryBlockBoundaryEnergyConstant (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (coarse : ℕ)
    (chosen : Fin (rule.generation coarse).edges) : ℝ :=
  ∑ edge, if markedGenerationConfiguration rule marks coarse [] true edge = true then
    (cellBoundaryIndicator (rule.generation coarse).network chosen ((rule.generation coarse).network.endpoint edge).1 -
      cellBoundaryIndicator (rule.generation coarse).network chosen ((rule.generation coarse).network.endpoint edge).2) ^ 2 /
      (growth⁻¹ ^ (coarse + 1) * field (generationEdgeAddress rule coarse edge)) else 0

def stationaryBlockComponentInverseConstant (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (coarse : ℕ)
    (chosen : Fin (rule.generation coarse).edges) : ℝ :=
  growth ^ (coarse + 1) * (1 + stationaryBlockBoundaryEnergyConstant rule marks field growth coarse chosen *
    (growth⁻¹ ^ (coarse + 1) * field (generationEdgeAddress rule coarse chosen)))

variable (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
  (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
  (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
  (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
  (stationary : ∀ address, electricalCell rule.network (marks (address, true))
    (fun edge => field (address ++ [edge])) = growth * field address)

include growthPositive fieldPositive in
theorem stationaryBlockBoundaryEnergyConstant_nonnegative (coarse : ℕ)
    (chosen : Fin (rule.generation coarse).edges) :
    0 ≤ stationaryBlockBoundaryEnergyConstant rule marks field growth coarse chosen := by
  classical
  apply Finset.sum_nonneg
  intro edge _
  split_ifs
  · exact div_nonneg (sq_nonneg _) (mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)).le
  · exact le_rfl

include growthPositive fieldPositive crossing stationary in
/-- One fixed finite coarse constant controls the inverse resistance of
every refinement of the actual component. Both B sides are included. -/
theorem stationary_actual_block_component_inverse_bound (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (first last : Fin (rule.generation fine).vertices)
    (firstRetained : ((rule.generation fine).network.openGraph
      (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
        (markedGenerationConfiguration rule marks coarse [] true chosen))).Reachable
      (plantedVertex (rule.generation fine).network sourceSide) first)
    (lastRetained : ((rule.generation fine).network.openGraph
      (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
        (markedGenerationConfiguration rule marks coarse [] true chosen))).Reachable
      (plantedVertex (rule.generation fine).network sourceSide) last) :
    pairResistance (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
        (markedGenerationConfiguration rule marks coarse [] true chosen)))
      (fun edge => stationaryGenerationResistance rule field growth fine (generationEdgeAddress rule coarse chosen) edge.val) first last ≤
      stationaryBlockComponentInverseConstant rule marks field growth coarse chosen *
      pairResistance (network (rule.generation (coarse + fine + 1)).network
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
        (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) [] edge.val)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex first)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex last) := by
  have scalarPositive : 0 < growth⁻¹ ^ (coarse + 1) := pow_pos (inv_pos.mpr growthPositive) _
  have scalarCancellation : growth ^ (coarse + 1) * growth⁻¹ ^ (coarse + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ growthPositive.ne', one_pow]
  have cellsIdentity : generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) =
      fun edge => markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse [] true edge) := by
    funext edge
    simpa only [List.nil_append] using generationBlockCells_marked rule marks coarse fine [] true edge
  have positiveWeights (edge : Fin (rule.generation (coarse + fine + 1)).edges) (_ : markedGenerationConfiguration rule marks (coarse + fine + 1) [] true edge = true) :
      0 < stationaryGenerationResistance rule field growth (coarse + fine + 1) [] edge :=
    mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)
  have childPair : pairResistance (network (rule.generation fine).network
      (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) chosen))
      (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) []
        ((generationBlockCellEmbedding rule coarse fine chosen).edge edge.val)) first last =
      growth⁻¹ ^ (coarse + 1) * pairResistance (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen)))
        (fun edge => stationaryGenerationResistance rule field growth fine (generationEdgeAddress rule coarse chosen) edge.val) first last := by
    rw [cellsIdentity]
    simp_rw [stationary_block_resistance_scaling]
    exact pairResistance_scale
      (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen)))
      (fun edge => stationaryGenerationResistance rule field growth fine (generationEdgeAddress rule coarse chosen) edge.val)
      (fun edge => (mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)).le)
      (growth⁻¹ ^ (coarse + 1)) scalarPositive.le first last
  have boundaryIdentity : cellBoundaryTestEnergy (rule.generation coarse).network (rule.generation fine).network
      (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
      (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) []
        ((generationBlockCellEmbedding rule coarse fine edge.1).edge edge.2.val)) chosen =
      stationaryBlockBoundaryEnergyConstant rule marks field growth coarse chosen := by
    rw [cellsIdentity]
    simp_rw [stationary_block_resistance_scaling]
    exact stationary_block_boundary_test_energy rule marks field growth growthPositive fieldPositive crossing stationary
      (rule.generation coarse).network (generationEdgeAddress rule coarse)
      (markedGenerationConfiguration rule marks coarse [] true) fine _ scalarPositive chosen
  have boundaryNonnegative := stationaryBlockBoundaryEnergyConstant_nonnegative rule marks field growth growthPositive fieldPositive coarse chosen
  have factorNonnegative : 0 ≤ stationaryBlockBoundaryEnergyConstant rule marks field growth coarse chosen *
      (growth⁻¹ ^ (coarse + 1) * field (generationEdgeAddress rule coarse chosen)) :=
    mul_nonneg boundaryNonnegative (mul_pos scalarPositive (fieldPositive _)).le
  have reachable := firstRetained.symm.trans lastRetained
  by_cases opened : markedGenerationConfiguration rule marks coarse [] true chosen = true
  · have cellCrossing : (rule.generation fine).network.crosses
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) chosen) = true := by
      rw [cellsIdentity, markedGenerationConfiguration_crosses rule marks crossing, opened]
    have terminalIdentity : (network (rule.generation fine).network
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) chosen)).effectiveResistance
        (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) []
          ((generationBlockCellEmbedding rule coarse fine chosen).edge edge.val)) =
        growth⁻¹ ^ (coarse + 1) * field (generationEdgeAddress rule coarse chosen) := by
      change electricalCell (rule.generation fine).network
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) chosen)
        (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) []
          ((generationBlockCellEmbedding rule coarse fine chosen).edge edge)) = _
      rw [cellsIdentity]
      dsimp only
      rw [opened]
      simp_rw [stationary_block_resistance_scaling]
      rw [electricalCell_scale (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen) true)
        (input := stationaryGenerationResistance rule field growth fine (generationEdgeAddress rule coarse chosen))
        (fun edge => (mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)).le)
        (scalar := growth⁻¹ ^ (coarse + 1)) scalarPositive.le,
        stationary_field_normalized_block_response rule marks field growth growthPositive fieldPositive crossing stationary]
    have comparison := actualBlock_component_resistance_lower_bound rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)
      (stationaryGenerationResistance rule field growth (coarse + fine + 1) []) positiveWeights chosen cellCrossing first last
      (by rwa [cellsIdentity])
    rw [childPair, boundaryIdentity, terminalIdentity] at comparison
    have scaled := mul_le_mul_of_nonneg_left comparison (pow_pos growthPositive (coarse + 1)).le
    simpa only [stationaryBlockComponentInverseConstant, ← mul_assoc, scalarCancellation, one_mul] using scaled
  · have closed : markedGenerationConfiguration rule marks coarse [] true chosen = false := Bool.eq_false_iff.mpr opened
    have cellNoncrossing : (rule.generation fine).network.crosses
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) chosen) = false := by
      rw [cellsIdentity, markedGenerationConfiguration_crosses rule marks crossing, closed]
    have identity := actualBlock_dangling_component_pairResistance_eq rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)
      (stationaryGenerationResistance rule field growth (coarse + fine + 1) []) positiveWeights chosen cellNoncrossing sourceSide first last
      (by rwa [cellsIdentity]) (by rwa [cellsIdentity])
    rw [childPair] at identity
    have nonnegative : 0 ≤ pairResistance (network (rule.generation (coarse + fine + 1)).network
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
        (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) [] edge.val)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex first)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex last) :=
      pairResistance_nonnegative_all
        (network (rule.generation (coarse + fine + 1)).network
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
        (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) [] edge.val)
        (fun edge => positiveWeights edge.val edge.property)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex first)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex last)
    have multiplied := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + stationaryBlockBoundaryEnergyConstant rule marks field growth coarse chosen *
      (growth⁻¹ ^ (coarse + 1) * field (generationEdgeAddress rule coarse chosen)) by linarith) nonnegative
    have scaled := mul_le_mul_of_nonneg_left multiplied (pow_pos growthPositive (coarse + 1)).le
    conv_lhs at scaled => rw [identity]
    simpa only [stationaryBlockComponentInverseConstant, ← mul_assoc, scalarCancellation, one_mul] using scaled

end
end IGSIII34.Diffusion
