import IGSIII34.ResistanceLimit.HarmonicTower
import IGSIII.Geometry.ActualBlockCellEmbedding

/-! Exact harmonic-tower restriction and minimization across arbitrary
actual generation blocks, derived from one-step minimizers. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

variable (rule : Rule)
  (configuration : ∀ depth, Configuration (rule.generation depth).edges)
  (coherent : configurationSequenceCoherent rule configuration)
  (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
  (minimizer : ∀ depth (boundary : Fin (rule.generation depth).vertices → ℝ),
    ∃ potential : Fin (rule.generation (depth + 1)).vertices → ℝ,
      (∀ vertex, ((rule.generation depth).network.openGraph (configuration depth)).Reachable
          (rule.generation depth).network.source vertex →
        potential (rule.generationOldVertex depth vertex) = boundary vertex) ∧
      sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
        (resistance (depth + 1)) potential =
      sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth) boundary)

include coherent in
theorem harmonicTower_block_boundary
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (vertex : RetainedSkeletonVertex (rule.generation coarse).network (configuration coarse)) :
    harmonicTower rule configuration resistance minimizer coarse boundary (coarse + fine + 1) (by omega)
      (blockOldVertexEmbedding rule coarse fine vertex.val) = boundary vertex.val := by
  have persistent := harmonicTower_persistent rule configuration coherent resistance minimizer coarse boundary
    coarse (coarse + fine + 1) le_rfl (by omega) vertex
  simpa only [retainedPersistentVertexEmbedding_val, ← blockOldVertexEmbedding_eq_persistent,
    harmonicTower, Nat.leRecOn_self] using persistent

include coherent in
theorem harmonicTower_block_minimal
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ) :
    sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network (configuration (coarse + fine + 1)))
      (resistance (coarse + fine + 1))
      (harmonicTower rule configuration resistance minimizer coarse boundary (coarse + fine + 1) (by omega)) =
    sourceComponentEnergy (network (rule.generation coarse).network (configuration coarse)) (resistance coarse)
      (fun vertex => harmonicTower rule configuration resistance minimizer coarse boundary (coarse + fine + 1) (by omega)
        (blockOldVertexEmbedding rule coarse fine vertex)) := by
  apply (harmonicTower_energy rule configuration resistance minimizer coarse boundary (coarse + fine + 1) (by omega)).trans
  symm
  apply sourceComponentEnergy_congr_retained
  intro vertex retained
  rw [graph_eq_openGraph] at retained
  exact harmonicTower_block_boundary rule configuration coherent resistance minimizer coarse fine boundary ⟨vertex, retained⟩

end
end IGSIII34.ResistanceLimit
