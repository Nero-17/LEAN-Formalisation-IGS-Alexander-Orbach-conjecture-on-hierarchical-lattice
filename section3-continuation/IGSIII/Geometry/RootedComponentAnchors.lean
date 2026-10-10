import IGSIII.Geometry.RootedComponentPersistence
import IGSIII.Geometry.CellLocalisationWeighted

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

def rootedFirstBoundaryVertex (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool) :
    RetainedComponentVertex (rule.generation 0).network (configuration 0) sourceSide :=
  ⟨plantedVertex (rule.generation 0).network sourceSide, SimpleGraph.Reachable.refl _⟩

def rootedSecondBoundaryVertex (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool) :
    RetainedComponentVertex (rule.generation 0).network (configuration 0) sourceSide := by
  classical
  exact if connected : ((rule.generation 0).network.openGraph (configuration 0)).Reachable
      (plantedVertex (rule.generation 0).network sourceSide) (plantedVertex (rule.generation 0).network (!sourceSide)) then
    ⟨plantedVertex (rule.generation 0).network (!sourceSide), connected⟩ else rootedFirstBoundaryVertex rule configuration sourceSide

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (scale : ℝ) (scalePositive : 0 < scale) (offset : ℕ)
variable (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ values depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < values depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + offset)) atTop (𝓝 (values coarse edge)))

def rootedFirstBoundaryAnchor : RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive offset
    values nonnegative positive childConvergence :=
  rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence
    0 (rootedFirstBoundaryVertex rule configuration sourceSide)

def rootedSecondBoundaryAnchor : RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive offset
    values nonnegative positive childConvergence :=
  rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence
    0 (rootedSecondBoundaryVertex rule configuration sourceSide)

theorem rootedFirstBoundaryAnchor_distance (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence depth vertex)
      (rootedFirstBoundaryAnchor rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence) =
    weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
      (indexedBondCost (rule.generation depth).network (values depth)) (plantedVertex (rule.generation depth).network sourceSide) vertex.val := by
  rw [dist_comm, rootedFirstBoundaryAnchor, rootedComponentVertex_persistent rule classicalRule configuration coherent sourceSide scale scalePositive offset
    values nonnegative positive childConvergence 0 depth (Nat.zero_le depth), rootedComponentVertex_distance]
  change weightedDistance _ _ (persistentVertexEmbedding rule 0 depth (Nat.zero_le depth) (plantedVertex (rule.generation 0).network sourceSide)) _ = _
  rw [persistentVertexEmbedding_planted]

theorem rootedSecondBoundaryAnchor_distance (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence depth vertex)
      (rootedSecondBoundaryAnchor rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence) =
    if ((rule.generation 0).network.openGraph (configuration 0)).Reachable
        (plantedVertex (rule.generation 0).network sourceSide) (plantedVertex (rule.generation 0).network (!sourceSide)) then
      weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
        (indexedBondCost (rule.generation depth).network (values depth)) (plantedVertex (rule.generation depth).network (!sourceSide)) vertex.val
    else weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
      (indexedBondCost (rule.generation depth).network (values depth)) (plantedVertex (rule.generation depth).network sourceSide) vertex.val := by
  classical
  unfold rootedSecondBoundaryAnchor rootedSecondBoundaryVertex
  split_ifs with connected
  · rw [dist_comm, rootedComponentVertex_persistent rule classicalRule configuration coherent sourceSide scale scalePositive offset
      values nonnegative positive childConvergence 0 depth (Nat.zero_le depth), rootedComponentVertex_distance]
    change weightedDistance _ _ (persistentVertexEmbedding rule 0 depth (Nat.zero_le depth) (plantedVertex (rule.generation 0).network (!sourceSide))) _ = _
    rw [persistentVertexEmbedding_planted]
  · exact rootedFirstBoundaryAnchor_distance rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence depth vertex

theorem rootedComponentBoundary_radius (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    min
      (dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence depth vertex)
        (rootedFirstBoundaryAnchor rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence))
      (dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence depth vertex)
        (rootedSecondBoundaryAnchor rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence)) =
    weightedComponentBoundaryDistance ((rule.generation depth).network.openGraph (configuration depth))
      (indexedBondCost (rule.generation depth).network (values depth))
      (rule.generation depth).network.source (rule.generation depth).network.target vertex.val := by
  classical
  rw [rootedFirstBoundaryAnchor_distance, rootedSecondBoundaryAnchor_distance]
  have otherReachable : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (plantedVertex (rule.generation depth).network (!sourceSide)) vertex.val ↔
      ((rule.generation 0).network.openGraph (configuration 0)).Reachable
        (plantedVertex (rule.generation 0).network sourceSide) (plantedVertex (rule.generation 0).network (!sourceSide)) := by
    have preservation := persistentVertexEmbedding_reachable_iff rule configuration coherent 0 depth (Nat.zero_le depth)
      (plantedVertex (rule.generation 0).network sourceSide) (plantedVertex (rule.generation 0).network (!sourceSide))
    rw [persistentVertexEmbedding_planted, persistentVertexEmbedding_planted] at preservation
    constructor
    · intro oppositeReached
      exact preservation.mp (vertex.property.trans oppositeReached.symm)
    · intro connected
      exact (preservation.mpr connected).symm.trans vertex.property
  have ownReachable := vertex.property
  cases sourceSide with
  | false =>
    simp only [plantedVertex, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at ownReachable otherReachable ⊢
    unfold weightedComponentBoundaryDistance
    by_cases sourceReached : ((rule.generation depth).network.openGraph (configuration depth)).Reachable (rule.generation depth).network.source vertex.val
    · simp only [if_pos sourceReached, if_pos ownReachable, if_pos (otherReachable.mp sourceReached), min_comm]
    · simp only [if_neg sourceReached, if_pos ownReachable, if_neg (fun connected => sourceReached (otherReachable.mpr connected)), min_self]
  | true =>
    simp only [plantedVertex, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ownReachable otherReachable ⊢
    unfold weightedComponentBoundaryDistance
    by_cases targetReached : ((rule.generation depth).network.openGraph (configuration depth)).Reachable (rule.generation depth).network.target vertex.val
    · simp only [if_pos ownReachable, if_pos targetReached, if_pos (otherReachable.mp targetReached)]
    · simp only [if_pos ownReachable, if_neg targetReached, if_neg (fun connected => targetReached (otherReachable.mpr connected)), min_self]

end
end IGSIII.Geometry

