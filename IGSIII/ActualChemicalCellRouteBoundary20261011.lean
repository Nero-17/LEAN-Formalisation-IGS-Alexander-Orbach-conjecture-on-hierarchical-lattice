import IGSIII.ActualChemicalCellRouteFinite20261011
import IGSIII.Geometry.RootedComponentAnchors

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem retainedChemicalBoundaryVertex_persistent20261011 (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (fine host : ℕ) (bound : fine ≤ host) (side : Bool) :
    retainedComponentPersistentEmbedding rule configuration coherent sourceSide fine host bound
      (retainedChemicalBoundaryVertex20261011 (rule.generation fine).network (configuration fine) sourceSide side) =
      retainedChemicalBoundaryVertex20261011 (rule.generation host).network (configuration host) sourceSide side := by
  classical
  apply Subtype.ext
  have connectedEquivalent := persistentVertexEmbedding_reachable_iff rule configuration coherent fine host bound
    (plantedVertex (rule.generation fine).network sourceSide) (plantedVertex (rule.generation fine).network (!sourceSide))
  rw [persistentVertexEmbedding_planted, persistentVertexEmbedding_planted] at connectedEquivalent
  cases side with
  | false =>
    exact persistentVertexEmbedding_planted rule fine host bound sourceSide
  | true =>
    by_cases connected : ((rule.generation fine).network.openGraph (configuration fine)).Reachable
        (plantedVertex (rule.generation fine).network sourceSide) (plantedVertex (rule.generation fine).network (!sourceSide))
    · simp only [retainedComponentPersistentEmbedding_val, retainedChemicalBoundaryVertex20261011,
        ↓reduceIte, dif_pos connected, dif_pos (connectedEquivalent.mpr connected)]
      exact persistentVertexEmbedding_planted rule fine host bound (!sourceSide)
    · have hostDisconnected := fun reached => connected (connectedEquivalent.mp reached)
      simp only [retainedComponentPersistentEmbedding_val, retainedChemicalBoundaryVertex20261011,
        ↓reduceIte, dif_neg connected, dif_neg hostDisconnected]
      exact persistentVertexEmbedding_planted rule fine host bound sourceSide

@[simp] theorem retainedChemicalBoundaryVertex_zero_false20261011 (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool) :
    retainedChemicalBoundaryVertex20261011 (rule.generation 0).network (configuration 0) sourceSide false =
      rootedFirstBoundaryVertex rule configuration sourceSide := rfl

@[simp] theorem retainedChemicalBoundaryVertex_zero_true20261011 (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool) :
    retainedChemicalBoundaryVertex20261011 (rule.generation 0).network (configuration 0) sourceSide true =
      rootedSecondBoundaryVertex rule configuration sourceSide := rfl

end
end IGSIII.Geometry

