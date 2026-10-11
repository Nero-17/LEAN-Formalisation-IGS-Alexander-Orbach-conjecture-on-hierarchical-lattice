import IGSIII34.ResistanceLimit.GenerationBlockFlatnessCompletion20261011
import IGSIII34.ResistanceLimit.ActualHarmonic

/-! Actual harmonic interpolation is constant on each retained component of
a flat coarse cell at every later generation. The trace-minimization input
is proved from the harmonic tower, rather than imposed as an extra axiom. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

theorem stationary_harmonic_tower_flat_cell
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (address : List (Fin rule.edges)) (opened : Bool)
    (coherent : configurationSequenceCoherent rule
      (fun depth => markedGenerationConfiguration rule marks depth address opened))
    (minimizer : ∀ depth (boundary : Fin (rule.generation depth).vertices → ℝ),
      ∃ potential : Fin (rule.generation (depth + 1)).vertices → ℝ,
        (∀ vertex, ((rule.generation depth).network.openGraph
            (markedGenerationConfiguration rule marks depth address opened)).Reachable
            (rule.generation depth).network.source vertex →
          potential (rule.generationOldVertex depth vertex) = boundary vertex) ∧
        sourceComponentEnergy (network (rule.generation (depth + 1)).network
          (markedGenerationConfiguration rule marks (depth + 1) address opened))
          (fun edge => stationaryGenerationResistance rule field growth (depth + 1) address edge.val) potential =
        sourceComponentEnergy (network (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth address opened))
          (fun edge => stationaryGenerationResistance rule field growth depth address edge.val) boundary)
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (edge : Fin (rule.generation coarse).edges)
    (flatAvailable : markedGenerationConfiguration rule marks coarse address opened edge = true →
      sourceProjection (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened)) boundary
        ((rule.generation coarse).network.endpoint edge).1 =
      sourceProjection (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened)) boundary
        ((rule.generation coarse).network.endpoint edge).2)
    (first last : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable first last)
    (firstRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex first))
    (lastRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex last)) :
    harmonicTower rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse boundary (coarse + fine + 1) (by omega) ((generationBlockCellEmbedding rule coarse fine edge).vertex first) =
    harmonicTower rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse boundary (coarse + fine + 1) (by omega) ((generationBlockCellEmbedding rule coarse fine edge).vertex last) := by
  have restriction (vertex : Fin (rule.generation coarse).vertices)
      (retained : ((rule.generation coarse).network.openGraph
        (markedGenerationConfiguration rule marks coarse address opened)).Reachable
        (rule.generation coarse).network.source vertex) :
      harmonicTower rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
        (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
        coarse boundary (coarse + fine + 1) (by omega) (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex := by
    have persistent := harmonicTower_persistent rule
      (fun depth => markedGenerationConfiguration rule marks depth address opened) coherent
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse boundary coarse (coarse + fine + 1) le_rfl (by omega) ⟨vertex, retained⟩
    simpa only [retainedPersistentVertexEmbedding_val, ← blockOldVertexEmbedding_eq_persistent,
      harmonicTower, Nat.leRecOn_self] using persistent
  have projection :
      sourceProjection (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened))
        (fun vertex => harmonicTower rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
          (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
          coarse boundary (coarse + fine + 1) (by omega) (blockOldVertexEmbedding rule coarse fine vertex)) =
      sourceProjection (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened)) boundary := by
    funext vertex
    by_cases retained : (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened)).graph.Reachable
        (network (rule.generation coarse).network
          (markedGenerationConfiguration rule marks coarse address opened)).source vertex
    · have retained' := retained
      rw [graph_eq_openGraph] at retained'
      simp only [sourceProjection, if_pos retained, restriction vertex retained']
    · simp only [sourceProjection, if_neg retained]
  refine stationary_generation_block_minimizer_flat_cell rule marks field growth growthPositive fieldPositive
    crossing stationary coarse fine address opened
    (harmonicTower rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse boundary (coarse + fine + 1) (by omega)) ?_ edge ?_ first last reachable firstRetained lastRetained
  · apply (harmonicTower_energy rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse boundary (coarse + fine + 1) (by omega)).trans
    symm
    apply sourceComponentEnergy_congr_retained
    intro vertex retained
    rw [graph_eq_openGraph] at retained
    exact restriction vertex retained
  · intro retained
    rw [congrFun projection _, congrFun projection _]
    exact flatAvailable retained

end
end IGSIII34.ResistanceLimit
