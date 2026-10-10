import IGSIII.Geometry.CellLocalisationSplitLimits
import IGSIII.Geometry.CellLocalisationEmbedding

set_option autoImplicit false
set_option maxHeartbeats 4000000
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
variable (coarse : ℕ) (edge : Fin (rule.generation coarse).edges)
variable (firstRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge true))
variable (componentLengths : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (componentConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) edge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (componentLengths age child)))

variable (closed : configuration coarse edge = false)
variable (secondRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge false))

variable (componentNonnegative : ∀ fine child, 0 ≤ componentLengths fine child)
variable (componentPositive : ∀ fine child,
  generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge child = true → 0 < componentLengths fine child)
include closed in
/-- The two completed sides of one noncrossing cell pay both intrinsic boundary radii, using their shared raw innovation tower. -/
theorem rootedComponentCompletionInclusion_noncrossing_boundary_separation
    (first : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)
    (last : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence) :
    min (dist first (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence))
        (dist first (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)) +
      min (dist last (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence))
        (dist last (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)) ≤
      dist ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge true firstRetained componentLengths componentConvergence componentNonnegative componentPositive) first) ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge false secondRetained componentLengths componentConvergence componentNonnegative componentPositive) last) := by
  have firstContinuous := (rootedComponentCompletionInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge true firstRetained
    componentLengths componentConvergence componentNonnegative componentPositive).continuous
  have secondContinuous := (rootedComponentCompletionInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge false secondRetained
    componentLengths componentConvergence componentNonnegative componentPositive).continuous
  induction first using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih first =>
    induction last using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih last =>
      obtain ⟨firstDepth, first, rfl⟩ := DirectLimit.exists_eq_mk _ first
      obtain ⟨secondDepth, last, rfl⟩ := DirectLimit.exists_eq_mk _ last
      change min
        (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence firstDepth first) (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence))
        (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence firstDepth first) (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)) +
        min (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence secondDepth last) (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence))
          (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence secondDepth last) (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)) ≤
        dist ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge true firstRetained componentLengths componentConvergence componentNonnegative componentPositive) (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence firstDepth first))
          ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge false secondRetained componentLengths componentConvergence componentNonnegative componentPositive) (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence secondDepth last))
      rw [rootedComponentVertex_persistent rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence firstDepth (max firstDepth secondDepth) (le_max_left _ _) first,
        rootedComponentVertex_persistent rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence secondDepth (max firstDepth secondDepth) (le_max_right _ _) last]
      rw [rootedComponentBoundary_radius, rootedComponentBoundary_radius,
        rootedComponentCompletionInclusion_vertex, rootedComponentCompletionInclusion_vertex]
      exact actualComponentFiniteInclusion_noncrossing_boundary_separation rule classicalRule configuration coherent scale scalePositive
        ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge firstRetained componentLengths componentConvergence closed secondRetained (max firstDepth secondDepth)
        (retainedComponentPersistentEmbedding rule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
          (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true firstDepth (max firstDepth secondDepth) (le_max_left _ _) first)
        (retainedComponentPersistentEmbedding rule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
          (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false secondDepth (max firstDepth secondDepth) (le_max_right _ _) last)

include closed in
/-- The two completed sides of a shared noncrossing cell can intersect only at their respective available planted anchors. -/
theorem rootedComponentCompletionInclusion_noncrossing_intersection_boundary
    (first : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)
    (last : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)
    (same_image : (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge true firstRetained componentLengths componentConvergence componentNonnegative componentPositive) first = (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge false secondRetained componentLengths componentConvergence componentNonnegative componentPositive) last) :
    (first = rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence ∨ first = rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence) ∧
    (last = rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence ∨ last = rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence) := by
  have bound := rootedComponentCompletionInclusion_noncrossing_boundary_separation rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge firstRetained componentLengths componentConvergence closed secondRetained
    componentNonnegative componentPositive first last
  rw [same_image, dist_self] at bound
  have firstNonnegativeRadius : 0 ≤ min (dist first (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence))
      (dist first (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) true scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)) := le_min dist_nonneg dist_nonneg
  have secondNonnegativeRadius : 0 ≤ min (dist last (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence))
      (dist last (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) false scale scalePositive (coarse + 1) componentLengths componentNonnegative componentPositive componentConvergence)) := le_min dist_nonneg dist_nonneg
  constructor
  · by_contra interior
    push Not at interior
    have positiveRadius := lt_min (dist_pos.mpr interior.1) (dist_pos.mpr interior.2)
    linarith
  · by_contra interior
    push Not at interior
    have positiveRadius := lt_min (dist_pos.mpr interior.1) (dist_pos.mpr interior.2)
    linarith

end
end IGSIII.Geometry


