import IGSIII34.ResistanceLimit.GenerationComponentBoundsCompletion20261011
import IGSIII34.ResistanceLimit.HarmonicTowerBlockMinimumCompletion20261011
import IGSIII34.ResistanceLimit.ActualAvailableAnchorRetainedCompletion20261011

/-! Actual harmonic interpolation differs from a reference by at most the
available boundary error. The harmonic minimization is proved by the tower. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem stationary_harmonic_tower_component_deviation_completion20261011
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
    (edge : Fin (rule.generation coarse).edges) (reference error : ℝ)
    (vertex : Fin (rule.generation fine).vertices)
    (boundaryDeviation : ∀ side : Bool,
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
        (plantedVertex (rule.generation fine).network side) vertex →
      |boundary (if side then ((rule.generation coarse).network.endpoint edge).1
        else ((rule.generation coarse).network.endpoint edge).2) - reference| ≤ error)
    (available : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
      (rule.generation fine).network.source vertex ∨
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
      (rule.generation fine).network.target vertex)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex)) :
    |harmonicTower rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse boundary (coarse + fine + 1) (by omega) ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex)
      - reference| ≤ error := by
  refine stationary_generation_block_minimizer_component_deviation_completion20261011 rule marks field growth
    growthPositive fieldPositive crossing stationary coarse fine address opened
    (harmonicTower rule (fun depth => markedGenerationConfiguration rule marks depth address opened)
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse boundary (coarse + fine + 1) (by omega))
    (harmonicTower_block_minimal rule (fun depth => markedGenerationConfiguration rule marks depth address opened) coherent
      (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
      coarse fine boundary) edge reference error vertex ?_ available retained
  intro terminal terminalBoundary terminalReachable _
  rcases terminalBoundary with rfl | rfl
  · have oldRetained := actual_available_block_anchor_retained_completion20261011 rule marks crossing coarse fine
      address opened edge true vertex terminalReachable retained
    change ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse address opened)).Reachable
      (rule.generation coarse).network.source ((rule.generation coarse).network.endpoint edge).1 at oldRetained
    rw [generationBlockCellEmbedding_source,
      harmonicTower_block_boundary rule (fun depth => markedGenerationConfiguration rule marks depth address opened) coherent
        (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
        coarse fine boundary ⟨((rule.generation coarse).network.endpoint edge).1, oldRetained⟩]
    exact boundaryDeviation true terminalReachable
  · have oldRetained := actual_available_block_anchor_retained_completion20261011 rule marks crossing coarse fine
      address opened edge false vertex terminalReachable retained
    change ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse address opened)).Reachable
      (rule.generation coarse).network.source ((rule.generation coarse).network.endpoint edge).2 at oldRetained
    rw [generationBlockCellEmbedding_target,
      harmonicTower_block_boundary rule (fun depth => markedGenerationConfiguration rule marks depth address opened) coherent
        (fun depth edge => stationaryGenerationResistance rule field growth depth address edge.val) minimizer
        coarse fine boundary ⟨((rule.generation coarse).network.endpoint edge).2, oldRetained⟩]
    exact boundaryDeviation false terminalReachable

end
end IGSIII34.ResistanceLimit
