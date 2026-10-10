import IGSIII.Geometry.CellLocalisationIntrinsic

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (ambientLengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
variable (ambientNonnegative : ∀ depth edge, 0 ≤ ambientLengths depth edge)
variable (ambientPositive : ∀ depth edge, configuration depth edge = true → 0 < ambientLengths depth edge)
variable (ambientConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (ambientLengths coarse edge)))
variable (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
variable (anchorRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide))
variable (componentLengths : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (componentConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) edge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (componentLengths age child)))

variable (componentNonnegative : ∀ fine child, 0 ≤ componentLengths fine child)
variable (componentPositive : ∀ fine child,
  generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge child = true → 0 < componentLengths fine child)

/-- The canonical map of a genuine planted component completion is injective;
its only possible identifications from the cone estimate are boundary points,
and those remain distinct at the actual finite level. -/
theorem rootedComponentCompletionInclusion_injective :
    Function.Injective (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive) := by
  apply cell_injective_of_boundary_localisation _
    (rootedFirstBoundaryAnchor rule classicalRule
      (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
      (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence)
    (rootedSecondBoundaryAnchor rule classicalRule
      (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
      (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence)
  · exact rootedComponentCompletionInclusion_localisation rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive
  · intro same_image
    dsimp only [rootedFirstBoundaryAnchor, rootedSecondBoundaryAnchor] at same_image ⊢
    rw [rootedComponentCompletionInclusion_vertex, rootedComponentCompletionInclusion_vertex] at same_image
    exact congrArg (rootedComponentVertex rule classicalRule
      (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
      (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence 0)
      (actualComponentFiniteInclusion_injective rule classicalRule configuration coherent scale scalePositive
        ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained 0 same_image)

/-- Compact intrinsic cells embed as closed subsets of the actual limit
cluster through their canonical, one-Lipschitz completion maps. -/
theorem rootedComponentCompletionInclusion_isClosedEmbedding
    [CompactSpace (RootedComponentSpace rule classicalRule
      (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
      (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence)] :
    Topology.IsClosedEmbedding (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive) :=
  (rootedComponentCompletionInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
    componentLengths componentConvergence componentNonnegative componentPositive).continuous.isClosedEmbedding
    (rootedComponentCompletionInclusion_injective rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive)

end
end IGSIII.Geometry
