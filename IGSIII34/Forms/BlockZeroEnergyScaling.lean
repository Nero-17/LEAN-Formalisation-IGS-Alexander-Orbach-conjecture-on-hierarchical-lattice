import IGSIII34.Forms.ComponentResistanceScaling
import IGSIII34.ResistanceLimit.SideSourceTrace
import IGSIII.Geometry.ActualBlockCellEmbedding

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

theorem sourceComponentEnergy_scale_resistance {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (graph : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (scalar : ℝ) (potential : Vertex → ℝ) :
    sourceComponentEnergy graph (fun edge => scalar * resistance edge) potential =
      scalar⁻¹ * sourceComponentEnergy graph resistance potential := by
  classical
  unfold sourceComponentEnergy finiteEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  dsimp only
  split_ifs <;> simp only [mul_inv_rev, zero_mul, mul_zero] <;> ring

theorem stationary_block_resistance_scaling (rule : Rule)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges) (child : Fin (rule.generation fine).edges) :
    stationaryGenerationResistance rule field growth (coarse + fine + 1) []
      ((generationBlockCellEmbedding rule coarse fine chosen).edge child) =
        growth⁻¹ ^ (coarse + 1) * stationaryGenerationResistance rule field growth fine
          (generationEdgeAddress rule coarse chosen) child := by
  unfold stationaryGenerationResistance
  change growth⁻¹ ^ (coarse + fine + 1 + 1) * field
      ([] ++ generationEdgeAddress rule (coarse + fine + 1)
        ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (chosen, child)))) = _
  rw [generationEdgeAddress_block]
  simp only [List.nil_append]
  rw [show coarse + fine + 1 + 1 = (coarse + 1) + (fine + 1) by omega, pow_add]
  ring

theorem stationary_block_side_energy_scaling (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges) (opened sourceSide : Bool)
    (potential : Fin (rule.generation fine).vertices → ℝ) :
    sourceComponentEnergy (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen) opened)) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) []
        ((generationBlockCellEmbedding rule coarse fine chosen).edge edge.val)) potential =
      growth ^ (coarse + 1) * sourceComponentEnergy (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen) opened)) sourceSide)
        (fun edge => stationaryGenerationResistance rule field growth fine
          (generationEdgeAddress rule coarse chosen) edge.val) potential := by
  simp_rw [stationary_block_resistance_scaling]
  rw [sourceComponentEnergy_scale_resistance, inv_pow, inv_inv]

end
end IGSIII34.Forms
