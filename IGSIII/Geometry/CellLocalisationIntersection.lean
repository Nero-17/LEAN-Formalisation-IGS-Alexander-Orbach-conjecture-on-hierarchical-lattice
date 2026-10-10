import IGSIII.Geometry.CellLocalisationSeparation
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
variable (coarse : ℕ)
variable (firstEdge secondEdge : Fin (rule.generation coarse).edges) (distinct : firstEdge ≠ secondEdge)
variable (firstSide secondSide : Bool)
variable (firstRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse firstEdge firstSide))
variable (secondRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse secondEdge secondSide))
variable (firstLengths secondLengths : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (firstConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) firstEdge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (firstLengths age child)))
variable (secondConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) secondEdge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (secondLengths age child)))

variable (firstNonnegative : ∀ fine child, 0 ≤ firstLengths fine child)
variable (firstPositive : ∀ fine child,
  generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge child = true → 0 < firstLengths fine child)
variable (secondNonnegative : ∀ fine child, 0 ≤ secondLengths fine child)
variable (secondPositive : ∀ fine child,
  generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge child = true → 0 < secondLengths fine child)

include distinct in
/-- The intrinsic boundary-distance sum separates the full completions of two
distinct actual cells in the same actual ambient cluster. -/
theorem rootedComponentCompletionInclusion_boundary_separation
    (first : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence)
    (last : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence) :
    min (dist first (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence))
        (dist first (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence)) +
      min (dist last (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence))
        (dist last (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence)) ≤
      dist ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse firstEdge firstSide firstRetained firstLengths firstConvergence firstNonnegative firstPositive) first) ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse secondEdge secondSide secondRetained secondLengths secondConvergence secondNonnegative secondPositive) last) := by
  have firstContinuous := (rootedComponentCompletionInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse firstEdge firstSide firstRetained
    firstLengths firstConvergence firstNonnegative firstPositive).continuous
  have secondContinuous := (rootedComponentCompletionInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse secondEdge secondSide secondRetained
    secondLengths secondConvergence secondNonnegative secondPositive).continuous
  induction first using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih first =>
    induction last using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih last =>
      obtain ⟨firstDepth, first, rfl⟩ := DirectLimit.exists_eq_mk _ first
      obtain ⟨secondDepth, last, rfl⟩ := DirectLimit.exists_eq_mk _ last
      change min
        (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence firstDepth first) (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence))
        (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence firstDepth first) (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence)) +
        min (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence secondDepth last) (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence))
          (dist (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence secondDepth last) (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence)) ≤
        dist ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse firstEdge firstSide firstRetained firstLengths firstConvergence firstNonnegative firstPositive) (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence firstDepth first))
          ((rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse secondEdge secondSide secondRetained secondLengths secondConvergence secondNonnegative secondPositive) (rootedComponentVertex rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence secondDepth last))
      rw [rootedComponentVertex_persistent rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence firstDepth (max firstDepth secondDepth) (le_max_left _ _) first,
        rootedComponentVertex_persistent rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence secondDepth (max firstDepth secondDepth) (le_max_right _ _) last]
      rw [rootedComponentBoundary_radius, rootedComponentBoundary_radius,
        rootedComponentCompletionInclusion_vertex, rootedComponentCompletionInclusion_vertex]
      exact actualComponentFiniteInclusion_boundary_separation rule classicalRule configuration coherent scale scalePositive
        ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse firstEdge secondEdge distinct firstSide secondSide
        firstRetained secondRetained firstLengths secondLengths firstConvergence secondConvergence (max firstDepth secondDepth)
        (retainedComponentPersistentEmbedding rule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge)
          (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide firstDepth (max firstDepth secondDepth) (le_max_left _ _) first)
        (retainedComponentPersistentEmbedding rule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge)
          (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide secondDepth (max firstDepth secondDepth) (le_max_right _ _) last)

include distinct in
/-- Distinct actual limit cells intersect only at their available planted
boundary anchors; a noncrossing side has just one such anchor. -/
theorem rootedComponentCompletionInclusion_intersection_boundary
    (first : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence)
    (last : RootedComponentSpace rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence)
    (same_image : (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse firstEdge firstSide firstRetained firstLengths firstConvergence firstNonnegative firstPositive) first = (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse secondEdge secondSide secondRetained secondLengths secondConvergence secondNonnegative secondPositive) last) :
    (first = rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence ∨ first = rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence) ∧
    (last = rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence ∨ last = rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence) := by
  have bound := rootedComponentCompletionInclusion_boundary_separation rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse firstEdge secondEdge distinct firstSide secondSide
    firstRetained secondRetained firstLengths secondLengths firstConvergence secondConvergence
    firstNonnegative firstPositive secondNonnegative secondPositive first last
  rw [same_image, dist_self] at bound
  have firstNonnegativeRadius : 0 ≤ min (dist first (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence))
      (dist first (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge) firstSide scale scalePositive (coarse + 1) firstLengths firstNonnegative firstPositive firstConvergence)) := le_min dist_nonneg dist_nonneg
  have secondNonnegativeRadius : 0 ≤ min (dist last (rootedFirstBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence))
      (dist last (rootedSecondBoundaryAnchor rule classicalRule (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) (generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge) secondSide scale scalePositive (coarse + 1) secondLengths secondNonnegative secondPositive secondConvergence)) := le_min dist_nonneg dist_nonneg
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
