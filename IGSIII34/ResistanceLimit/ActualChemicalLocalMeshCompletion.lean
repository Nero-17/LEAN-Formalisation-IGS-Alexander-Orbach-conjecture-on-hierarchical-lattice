import IGSIII.Geometry.ActualBlockComponentLimits

/-! The chemical available-terminal mesh of the original retained cluster,
obtained from its actual microscopic terminal-component radii. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

theorem actual_chemical_local_component_mesh_completion
    (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (configurationIdentity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scalePositive : 0 < scale)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (positive : ∀ depth edge, configuration depth edge = true → 0 < lengths depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (configuration (coarse + fine + 1)) edge)).dist
        (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (coarse fine : ℕ) (beyond : start ≤ coarse)
    (edge : Fin (rule.generation coarse).edges) (side : Bool)
    (vertex : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (configuration (coarse + fine + 1)) edge)).Reachable (plantedVertex (rule.generation fine).network side) vertex)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph (configuration (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex)) :
    ∃ anchorRetained : ((rule.generation (coarse + fine + 1)).network.openGraph (configuration (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side)),
    dist (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
      (coarse + fine + 1) ⟨_,anchorRetained⟩)
      (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
        (coarse + fine + 1) ⟨_,retained⟩) ≤ coefficient * eta ^ (coarse + 1) := by
  have anchorRetained := retained.trans ((reachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom
    (configuration (coarse + fine + 1)))).symm)
  refine ⟨anchorRetained, actualChemicalVertex_dist_block_le rule classicalRule configuration coherent scale scalePositive lengths
    nonnegative positive childConvergence coarse fine edge side vertex reachable anchorRetained retained
    (coefficient * eta ^ (coarse + 1)) ?_⟩
  intro host point localReachable
  have componentBound := generationBlockCellEmbedding_distance_to_planted_le rule coarse host edge
    (configuration (coarse + host + 1)) side point localReachable
  have componentBoundReal : (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
      ((generationBlockCellEmbedding rule coarse host edge).vertex (plantedVertex (rule.generation host).network side))
      ((generationBlockCellEmbedding rule coarse host edge).vertex point) : ℝ) ≤
      (terminalComponentRadius (rule.generation host).network (generationBlockCells rule coarse host
        (configuration (coarse + host + 1)) edge) : ℝ) := by exact_mod_cast componentBound
  have normalized := div_le_div_of_nonneg_right componentBoundReal (pow_pos scalePositive (coarse + host + 2)).le
  have cellRadius := radiusBounds (generationEdgeAddress rule coarse edge) (configuration coarse edge) host
    (by rw [generationEdgeAddress_length]; omega)
  rw [generationEdgeAddress_length] at cellRadius
  rw [configurationIdentity (coarse + host + 1), generationBlockCells_marked, List.nil_append] at normalized
  rw [configurationIdentity coarse] at cellRadius
  rw [configurationIdentity (coarse + host + 1)]
  exact normalized.trans (by simpa only [markedTerminalComponentRadius, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius)

end
end IGSIII34.ResistanceLimit
