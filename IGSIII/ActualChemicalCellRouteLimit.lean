import IGSIII.ActualChemicalCellRouteFinite
import IGSIII.ActualChemicalCellRouteBoundary
import IGSIII.Geometry.CellLocalisationIntrinsic

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

def boundaryRouteCost {Local : Type*} (intrinsic ambient : Local → Local → ℝ)
    (boundary : Bool → Local) (first last : Local) : ℝ :=
  min (intrinsic first last)
    (min
      (min (intrinsic first (boundary false) + ambient (boundary false) (boundary false) + intrinsic (boundary false) last)
        (intrinsic first (boundary false) + ambient (boundary false) (boundary true) + intrinsic (boundary true) last))
      (min (intrinsic first (boundary true) + ambient (boundary true) (boundary false) + intrinsic (boundary false) last)
        (intrinsic first (boundary true) + ambient (boundary true) (boundary true) + intrinsic (boundary true) last)))

theorem boundaryRouteCost_tendsto {Local : Type*}
    (intrinsic ambient : ℕ → Local → Local → ℝ)
    (intrinsicLimit ambientLimit : Local → Local → ℝ)
    (intrinsicConvergence : ∀ first last, Tendsto (fun depth => intrinsic depth first last) atTop (𝓝 (intrinsicLimit first last)))
    (ambientConvergence : ∀ first last, Tendsto (fun depth => ambient depth first last) atTop (𝓝 (ambientLimit first last)))
    (boundary : Bool → Local) (first last : Local) :
    Tendsto (fun depth => boundaryRouteCost (intrinsic depth) (ambient depth) boundary first last) atTop
      (𝓝 (boundaryRouteCost intrinsicLimit ambientLimit boundary first last)) := by
  have routeLimit (exit entrance : Bool) :=
    ((intrinsicConvergence first (boundary exit)).add (ambientConvergence (boundary exit) (boundary entrance))).add
      (intrinsicConvergence (boundary entrance) last)
  exact (intrinsicConvergence first last).min
    (((routeLimit false false).min (routeLimit false true)).min
      ((routeLimit true false).min (routeLimit true true)))

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

/-- The actual inclusion distance is the limit of its original microscopic
block distances, with both vertex labels retained. -/
theorem actualComponentFiniteInclusion_microscopic_limit (fine : ℕ)
    (first last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
    Tendsto (fun host => if beyond : fine ≤ host then
      (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
        ((generationBlockCellEmbedding rule coarse host edge).vertex (persistentVertexEmbedding rule fine host beyond first.val))
        ((generationBlockCellEmbedding rule coarse host edge).vertex (persistentVertexEmbedding rule fine host beyond last.val)) : ℝ) /
          scale ^ (coarse + host + 2) else 0) atTop
      (𝓝 (dist
        (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
          ambientConvergence coarse edge sourceSide anchorRetained fine first)
        (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
          ambientConvergence coarse edge sourceSide anchorRetained fine last))) := by
  have firstRetained := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained first).property
  have lastRetained := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained last).property
  have ambientLimit := (actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive
    (coarse + fine + 1) (ambientLengths (coarse + fine + 1)) (ambientConvergence (coarse + fine + 1))
    (firstRetained.symm.trans lastRetained)).comp (tendsto_add_atTop_nat (coarse + 1))
  rw [actualComponentFiniteInclusion, actualComponentFiniteInclusion, actualChemicalVertex_distance]
  apply ambientLimit.congr'
  filter_upwards [eventually_ge_atTop fine] with host beyond
  dsimp only [Function.comp_apply]
  rw [show host + (coarse + 1) = coarse + host + 1 by omega]
  simp only [persistentNormalizedDistance, dif_pos (show coarse + fine + 1 ≤ coarse + host + 1 by omega), dif_pos beyond]
  change (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
    (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex first.val))
    (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex last.val)) : ℝ) / scale ^ (coarse + host + 1 + 1) = _
  rw [generationBlockCellEmbedding_persistent rule coarse fine host beyond edge first.val,
    generationBlockCellEmbedding_persistent rule coarse fine host beyond edge last.val]

include componentConvergence in
/-- Exact first-exit identity on the actual limiting finite skeleton, obtained
from the same microscopic block configurations on both sides. -/
theorem actualComponentFiniteInclusion_route_equality (fine : ℕ)
    (first last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
    letI := retainedComponentMetric (rule.generation fine).network (classicalRule.generation fine).simple
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide
      (componentLengths fine) (componentNonnegative fine) (componentPositive fine)
    dist
      (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
        ambientConvergence coarse edge sourceSide anchorRetained fine first)
      (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
        ambientConvergence coarse edge sourceSide anchorRetained fine last) =
      twoBoundaryRouteDistance
        (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
          ambientConvergence coarse edge sourceSide anchorRetained fine)
        (retainedChemicalBoundaryVertex (rule.generation fine).network
          (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) first last := by
  classical
  let childConfiguration := fun age => generationBlockCells rule coarse age (configuration (coarse + age + 1)) edge
  have childCoherent := generationBlockCells_sequence_coherent rule configuration coherent coarse edge
  letI := retainedComponentMetric (rule.generation fine).network (classicalRule.generation fine).simple
    (childConfiguration fine) sourceSide (componentLengths fine) (componentNonnegative fine) (componentPositive fine)
  let intrinsicMicroscopic := fun host (first last : RetainedComponentVertex (rule.generation fine).network (childConfiguration fine) sourceSide) =>
    persistentNormalizedDistance rule childConfiguration scale fine first.val last.val host / scale ^ (coarse + 1)
  let ambientMicroscopic := fun host (first last : RetainedComponentVertex (rule.generation fine).network (childConfiguration fine) sourceSide) =>
    if beyond : fine ≤ host then
      (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
        ((generationBlockCellEmbedding rule coarse host edge).vertex (persistentVertexEmbedding rule fine host beyond first.val))
        ((generationBlockCellEmbedding rule coarse host edge).vertex (persistentVertexEmbedding rule fine host beyond last.val)) : ℝ) /
        scale ^ (coarse + host + 2) else 0
  let inclusion := actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive
    ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained fine
  let boundary := retainedChemicalBoundaryVertex (rule.generation fine).network (childConfiguration fine) sourceSide
  have intrinsicLimit : ∀ first last, Tendsto (fun host => intrinsicMicroscopic host first last) atTop (𝓝 (dist first last)) := by
    intro first last
    exact actual_persistent_skeleton_distances_tendsto_offset rule classicalRule childConfiguration childCoherent scale scalePositive
      (coarse + 1) fine componentLengths componentConvergence (first.property.symm.trans last.property)
  have ambientLimit : ∀ first last, Tendsto (fun host => ambientMicroscopic host first last) atTop
      (𝓝 (dist (inclusion first) (inclusion last))) := by
    intro first last
    exact actualComponentFiniteInclusion_microscopic_limit rule classicalRule configuration coherent scale scalePositive
      ambientLengths ambientNonnegative ambientPositive ambientConvergence coarse edge sourceSide anchorRetained fine first last
  have routeLimit := boundaryRouteCost_tendsto intrinsicMicroscopic ambientMicroscopic
    (fun first last => dist first last) (fun first last => dist (inclusion first) (inclusion last))
    intrinsicLimit ambientLimit boundary first last
  apply tendsto_nhds_unique (ambientLimit first last)
  apply routeLimit.congr'
  filter_upwards [eventually_ge_atTop fine] with host beyond
  have boundaryPersistence (side : Bool) := congrArg Subtype.val
    (retainedChemicalBoundaryVertex_persistent rule childConfiguration childCoherent sourceSide fine host beyond side)
  have finiteIdentity := generationBlockCellEmbedding_route_equality rule coarse host
    (configuration (coarse + host + 1)) edge sourceSide
    (retainedComponentPersistentEmbedding rule childConfiguration childCoherent sourceSide fine host beyond first)
    (retainedComponentPersistentEmbedding rule childConfiguration childCoherent sourceSide fine host beyond last)
  change weightedDistance _ (fun _ => 1) _ _ =
    boundaryRouteCost
      (fun first last => weightedDistance ((rule.generation host).network.openGraph (childConfiguration host))
        (fun _ => 1) first.val last.val)
      (fun first last => weightedDistance ((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1)))
        (fun _ => 1) ((generationBlockCellEmbedding rule coarse host edge).vertex first.val)
        ((generationBlockCellEmbedding rule coarse host edge).vertex last.val))
      (retainedChemicalBoundaryVertex (rule.generation host).network (childConfiguration host) sourceSide) _ _ at finiteIdentity
  have scaledIdentity := congrArg (fun value : ℝ => value / scale ^ (coarse + host + 2)) finiteIdentity
  simp only [boundaryRouteCost, weightedDistance_unit_eq_dist,
    ← min_div_div_right (pow_pos scalePositive (coarse + host + 2)).le, add_div,
    ← boundaryPersistence false, ← boundaryPersistence true, retainedComponentPersistentEmbedding_val] at scaledIdentity
  have denominatorIdentity : scale ^ (host + 1) * scale ^ (coarse + 1) = scale ^ (coarse + host + 2) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [boundaryRouteCost, intrinsicMicroscopic, ambientMicroscopic,
    persistentNormalizedDistance, dif_pos beyond, div_div, denominatorIdentity, boundary] using scaledIdentity.symm

end
end IGSIII.Geometry
