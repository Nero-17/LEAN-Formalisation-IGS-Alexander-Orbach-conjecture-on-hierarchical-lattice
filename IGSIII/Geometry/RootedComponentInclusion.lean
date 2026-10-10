import IGSIII.Geometry.RootedComponentSkeleton
import IGSIII.Geometry.ActualBlockComponentLimits

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

def coarseCellPlantedVertex (rule : Rule) (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    Fin (rule.generation coarse).vertices :=
  if sourceSide then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2

theorem generationBlockCellEmbedding_planted (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool) :
    (generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network sourceSide) =
      persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) (coarseCellPlantedVertex rule coarse edge sourceSide) := by
  cases sourceSide with
  | false => simpa only [plantedVertex, Bool.false_eq_true, ↓reduceIte, coarseCellPlantedVertex] using
      (generationBlockCellEmbedding_target rule coarse fine edge).trans (blockOldVertexEmbedding_eq_persistent rule coarse fine _)
  | true => simpa only [plantedVertex, ↓reduceIte, coarseCellPlantedVertex] using
      (generationBlockCellEmbedding_source rule coarse fine edge).trans (blockOldVertexEmbedding_eq_persistent rule coarse fine _)

def retainedBlockComponentEmbedding (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (anchorRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide)) :
    RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide ↪
      RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network (configuration (coarse + fine + 1)) where
  toFun vertex := ⟨(generationBlockCellEmbedding rule coarse fine edge).vertex vertex.val, by
    have preserved := (persistentVertexEmbedding_reachable_iff rule configuration coherent coarse (coarse + fine + 1) (by omega)
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide)).mpr anchorRetained
    have sourceIdentity := persistentVertexEmbedding_planted rule coarse (coarse + fine + 1) (by omega) true
    change persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) (rule.generation coarse).network.source =
      (rule.generation (coarse + fine + 1)).network.source at sourceIdentity
    rw [sourceIdentity, ← generationBlockCellEmbedding_planted] at preserved
    exact preserved.trans (vertex.property.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom (configuration (coarse + fine + 1))))⟩
  inj' := by
    intro first last sameImage
    exact Subtype.ext ((generationBlockCellEmbedding rule coarse fine edge).vertex.injective (congrArg Subtype.val sameImage))

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

def actualComponentFiniteInclusion (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
    ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence :=
  actualChemicalVertex rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
    ambientConvergence (coarse + fine + 1) (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained vertex)

include componentConvergence in
/-- The inclusion compares limits of actual microscopic graph distances.
No intrinsic-to-ambient metric inequality is assumed. -/
theorem actualComponentFiniteInclusion_distance_le (fine : ℕ)
    (first last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
    dist (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained fine first)
      (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
        ambientConvergence coarse edge sourceSide anchorRetained fine last) ≤
    weightedDistance ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge))
      (indexedBondCost (rule.generation fine).network (componentLengths fine)) first.val last.val := by
  let childConfiguration := fun age => generationBlockCells rule coarse age (configuration (coarse + age + 1)) edge
  have childCoherent := generationBlockCells_sequence_coherent rule configuration coherent coarse edge
  have firstRetained := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained first).property
  have lastRetained := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained last).property
  have ambientLimit := (actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive
    (coarse + fine + 1) (ambientLengths (coarse + fine + 1)) (ambientConvergence (coarse + fine + 1))
    (firstRetained.symm.trans lastRetained)).comp (tendsto_add_atTop_nat (coarse + 1))
  have childLimit := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule childConfiguration childCoherent scale scalePositive
    (coarse + 1) fine componentLengths componentConvergence (first.property.symm.trans last.property)
  rw [actualComponentFiniteInclusion, actualComponentFiniteInclusion, actualChemicalVertex_distance]
  apply le_of_tendsto_of_tendsto ambientLimit childLimit
  filter_upwards [eventually_ge_atTop fine] with host beyond
  dsimp only [Function.comp_apply]
  rw [show host + (coarse + 1) = coarse + host + 1 by omega]
  simp only [persistentNormalizedDistance, dif_pos (show coarse + fine + 1 ≤ coarse + host + 1 by omega), dif_pos beyond]
  change (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
    (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex first.val))
    (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex last.val)) : ℝ) / scale ^ (coarse + host + 1 + 1) ≤ _
  rw [generationBlockCellEmbedding_persistent rule coarse fine host beyond edge first.val,
    generationBlockCellEmbedding_persistent rule coarse fine host beyond edge last.val]
  have reached := (persistentVertexEmbedding_reachable_iff rule childConfiguration childCoherent fine host beyond first.val last.val).mpr
    (first.property.symm.trans last.property)
  have graphBound := generationBlockCellEmbedding_distance_le rule coarse host edge (configuration (coarse + host + 1))
    (persistentVertexEmbedding rule fine host beyond first.val) (persistentVertexEmbedding rule fine host beyond last.val) reached
  rw [div_div]
  have denominatorIdentity : scale ^ (host + 1) * scale ^ (coarse + 1) = scale ^ (coarse + host + 1 + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [denominatorIdentity]
  exact div_le_div_of_nonneg_right (by exact_mod_cast graphBound) (pow_pos scalePositive (coarse + host + 1 + 1)).le

theorem actualComponentFiniteInclusion_transition (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedComponentVertex (rule.generation first).network
      (generationBlockCells rule coarse first (configuration (coarse + first + 1)) edge) sourceSide) :
    actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained first vertex =
    actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained second
      (Universality.Geometry.IsometricSequence.transition
        (fun fine => RetainedComponentVertex (rule.generation fine).network
          (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide)
        (retainedComponentOldEmbedding rule
          (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
          (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide) first second bound vertex) := by
  unfold actualComponentFiniteInclusion
  rw [actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
    ambientConvergence (coarse + first + 1) (coarse + second + 1) (by omega)]
  apply congrArg (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
    ambientConvergence (coarse + second + 1))
  apply Subtype.ext
  change persistentVertexEmbedding rule (coarse + first + 1) (coarse + second + 1) (by omega)
    ((generationBlockCellEmbedding rule coarse first edge).vertex vertex.val) = _
  rw [generationBlockCellEmbedding_persistent rule coarse first second bound edge vertex.val]
  change _ = (generationBlockCellEmbedding rule coarse second edge).vertex _
  rw [retainedComponentTransition_val]

variable (componentNonnegative : ∀ fine child, 0 ≤ componentLengths fine child)
variable (componentPositive : ∀ fine child,
  generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge child = true → 0 < componentLengths fine child)

def rootedComponentSkeletonInclusion :
    RootedComponentSkeleton rule classicalRule
      (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
      (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence →
    ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence :=
  DirectLimit.lift
    (Universality.Geometry.IsometricSequence.transition
      (fun fine => RetainedComponentVertex (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide)
      (retainedComponentOldEmbedding rule
        (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
        (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide))
    (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained)
    (actualComponentFiniteInclusion_transition rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained)

theorem rootedComponentSkeletonInclusion_mk (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
    rootedComponentSkeletonInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence componentNonnegative componentPositive
      ⟦⟨fine, vertex⟩⟧ =
    actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained fine vertex := rfl

theorem rootedComponentSkeletonInclusion_lipschitz :
    LipschitzWith 1 (rootedComponentSkeletonInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive) := by
  letI (fine : ℕ) := retainedComponentMetric (rule.generation fine).network (classicalRule.generation fine).simple
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide
    (componentLengths fine) (componentNonnegative fine) (componentPositive fine)
  apply LipschitzWith.of_dist_le_mul
  intro first last
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun fine => RetainedComponentVertex (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide)
      (retainedComponentOldEmbedding rule
        (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
        (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide))
    (fun fine first last => ?_) first last
  rw [rootedComponentSkeletonInclusion_mk, rootedComponentSkeletonInclusion_mk]
  simp only [NNReal.coe_one, one_mul]
  change _ ≤ Universality.Geometry.MetricDirectLimit.compatibleDistance _ _ _ _ _
  rw [Universality.Geometry.MetricDirectLimit.compatibleDistance_mk]
  exact actualComponentFiniteInclusion_distance_le rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
    ambientConvergence coarse edge sourceSide anchorRetained componentLengths componentConvergence fine first last

def rootedComponentCompletionInclusion :
    RootedComponentSpace rule classicalRule
      (fun fine => generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)
      (generationBlockCells_sequence_coherent rule configuration coherent coarse edge) sourceSide scale scalePositive (coarse + 1)
      componentLengths componentNonnegative componentPositive componentConvergence →
    ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence :=
  UniformSpace.Completion.extension (rootedComponentSkeletonInclusion rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
    componentLengths componentConvergence componentNonnegative componentPositive)

theorem rootedComponentCompletionInclusion_lipschitz :
    LipschitzWith 1 (rootedComponentCompletionInclusion rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
      componentLengths componentConvergence componentNonnegative componentPositive) :=
  (rootedComponentSkeletonInclusion_lipschitz rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained
    componentLengths componentConvergence componentNonnegative componentPositive).completion_extension

end
end IGSIII.Geometry
