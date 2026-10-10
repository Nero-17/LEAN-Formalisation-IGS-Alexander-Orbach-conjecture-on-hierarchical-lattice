import IGSIII.Geometry.CellLocalisationInclusion
import IGSIII.Geometry.CellLocalisationCompletion
import IGSIII.Geometry.RootedComponentAnchors

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

/-- Every finite stage of the actual component inclusion is injective. -/
theorem actualComponentFiniteInclusion_injective (fine : ℕ) :
    Function.Injective (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained fine) := by
  intro first last equal
  apply (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained).injective
  apply Subtype.ext
  have zeroDistance : weightedDistance
      ((rule.generation (coarse + fine + 1)).network.openGraph (configuration (coarse + fine + 1)))
      (indexedBondCost (rule.generation (coarse + fine + 1)).network (ambientLengths (coarse + fine + 1)))
      (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained first).val
      (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained last).val = 0 := by
    rw [← actualChemicalVertex_distance rule classicalRule configuration coherent scale scalePositive ambientLengths
      ambientNonnegative ambientPositive ambientConvergence]
    exact dist_eq_zero.mpr equal
  exact eq_of_weightedDistance_eq_zero_of_edge_positive _ _
    (indexedBondCost_nonnegative _ _ (ambientNonnegative (coarse + fine + 1)))
    (indexedBondCost_positive_on_open_edges _ (classicalRule.generation (coarse + fine + 1)).simple _ _
      (ambientPositive (coarse + fine + 1)))
    ((retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained first).property.symm.trans
      (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained last).property)
    zeroDistance

variable (componentNonnegative : ∀ fine child, 0 ≤ componentLengths fine child)
variable (componentPositive : ∀ fine child,
  generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge child = true → 0 < componentLengths fine child)

/-- The completion map extends the original indexed microscopic inclusions. -/
theorem rootedComponentCompletionInclusion_vertex (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
    rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive
      (rootedComponentVertex rule classicalRule
        (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
        (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
        componentLengths componentNonnegative componentPositive componentConvergence fine vertex) =
    actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained fine vertex := by
  exact UniformSpace.Completion.extension_coe
    (rootedComponentSkeletonInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive).uniformContinuous _

/-- First-exit localisation holds on the actual intrinsic completion. The
second boundary anchor repeats the first for a noncrossing planted component. -/
theorem rootedComponentCompletionInclusion_localisation
    (first last : RootedComponentSpace rule classicalRule
      (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
      (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence) :
    min (min
      (dist first (rootedFirstBoundaryAnchor rule classicalRule
        (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
        (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
        componentLengths componentNonnegative componentPositive componentConvergence))
      (dist first (rootedSecondBoundaryAnchor rule classicalRule
        (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
        (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
        componentLengths componentNonnegative componentPositive componentConvergence))) (dist first last) ≤
    dist (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive first)
      (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
        ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
        componentLengths componentConvergence componentNonnegative componentPositive last) := by
  have continuousInclusion := (rootedComponentCompletionInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
    componentLengths componentConvergence componentNonnegative componentPositive).continuous
  refine UniformSpace.Completion.induction_on₂ first last (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro first last
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun fine => RetainedComponentVertex (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide)
      (retainedComponentOldEmbedding rule
        (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
        (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide))
    (fun fine first last => ?_) first last
  change min (min
    (dist (rootedComponentVertex rule classicalRule _ _ sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence fine first) _)
    (dist (rootedComponentVertex rule classicalRule _ _ sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence fine first) _))
    (dist (rootedComponentVertex rule classicalRule _ _ sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence fine first)
      (rootedComponentVertex rule classicalRule _ _ sourceSide scale scalePositive (coarse + 1)
        componentLengths componentNonnegative componentPositive componentConvergence fine last)) ≤
    dist (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive
      (rootedComponentVertex rule classicalRule _ _ sourceSide scale scalePositive (coarse + 1)
        componentLengths componentNonnegative componentPositive componentConvergence fine first))
      (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
        ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
        componentLengths componentConvergence componentNonnegative componentPositive
        (rootedComponentVertex rule classicalRule _ _ sourceSide scale scalePositive (coarse + 1)
          componentLengths componentNonnegative componentPositive componentConvergence fine last))
  rw [rootedComponentBoundary_radius, rootedComponentVertex_distance,
    rootedComponentCompletionInclusion_vertex, rootedComponentCompletionInclusion_vertex]
  exact actualComponentFiniteInclusion_localisation rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
    ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence fine first last

end
end IGSIII.Geometry
