import IGSIII34.Diffusion.OriginalGenerationTraceRecoveryCompletion20261011
import IGSIII34.ResistanceLimit.HarmonicTower

/-! The exact microscopic source trace minimizer can be chosen globally
bounded by its retained coarse boundary, without removing hanging branches. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem exists_original_generation_bounded_trace_minimizer_completion20261011
    (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (scalar : ℝ) (scalarPositive : 0 < scalar)
    (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (boundaryBound : ∀ vertex, (network (rule.generation coarse).network
      ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration))).graph.Reachable
      (rule.generation coarse).network.source vertex → |boundary vertex| ≤ bound) :
    ∃ potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ,
      (∀ vertex, |potential vertex| ≤ bound) ∧
      (∀ vertex, (network (rule.generation coarse).network
        ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration))).graph.Reachable
        (rule.generation coarse).network.source vertex → potential (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex) ∧
      sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network configuration) (fun _ => scalar) potential =
      sourceComponentEnergy (network (rule.generation coarse).network
        ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration)))
        (fun edge => scalar * unitConfigurationResistance (rule.generation fine).network
          (generationBlockCells rule coarse fine configuration edge.val)) boundary := by
  classical
  obtain ⟨potential, restriction, minimizing⟩ := exists_original_generation_trace_minimizer_completion20261011
    rule coarse fine configuration scalar scalarPositive boundary
  let clip (value : ℝ) := max (-bound) (min value bound)
  have clipLipschitz : LipschitzWith 1 clip := (LipschitzWith.id.min_const bound).const_max (-bound)
  have clippedRestriction : ∀ vertex, (network (rule.generation coarse).network
      ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration))).graph.Reachable
      (rule.generation coarse).network.source vertex → clip (potential (blockOldVertexEmbedding rule coarse fine vertex)) = boundary vertex := by
    intro vertex retained
    rw [restriction vertex retained]
    dsimp only [clip]
    rw [min_eq_left (abs_le.mp (boundaryBound vertex retained)).2, max_eq_right (abs_le.mp (boundaryBound vertex retained)).1]
  refine ⟨fun vertex => clip (potential vertex), ?_, clippedRestriction, ?_⟩
  · intro vertex
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  · have decrease := finiteEnergy_normal_contraction
      (network (rule.generation (coarse + fine + 1)).network configuration).endpoint
      (fun edge => @ite ℝ ((network (rule.generation (coarse + fine + 1)).network configuration).graph.Reachable
        (network (rule.generation (coarse + fine + 1)).network configuration).source
        ((network (rule.generation (coarse + fine + 1)).network configuration).endpoint edge).1) (Classical.propDecidable _) scalar⁻¹ 0)
      (by intro edge; split_ifs; exact (inv_pos.mpr scalarPositive).le; exact le_rfl)
      clip (by
        intro first last
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using clipLipschitz.dist_le_mul first last) potential
    change sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network configuration)
      (fun _ => scalar) (fun vertex => clip (potential vertex)) ≤
      sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network configuration) (fun _ => scalar) potential at decrease
    have lower := original_generation_trace_energy_le_completion20261011 rule coarse fine configuration scalar scalarPositive
      (fun vertex => clip (potential vertex))
    have boundaryEnergy := sourceComponentEnergy_congr_retained
      (network (rule.generation coarse).network
        ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration)))
      (fun edge => scalar * unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine configuration edge.val))
      (fun vertex => clip (potential (blockOldVertexEmbedding rule coarse fine vertex))) boundary clippedRestriction
    rw [boundaryEnergy] at lower
    exact le_antisymm (decrease.trans_eq minimizing) lower

end
end IGSIII34.ResistanceLimit

