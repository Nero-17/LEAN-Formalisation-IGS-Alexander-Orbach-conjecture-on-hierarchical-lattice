import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCanonicalPath
import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open IGSIII34.Diffusion IGSIII34.ResistanceLimit
open scoped NNReal

theorem actualFiniteAnnealedNaturalClock_original_identity
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (resistanceScale : ℝ) (resistancePositive : 0 < resistanceScale) (kind : Fin 3) :
    (actualFiniteAnnealedNaturalClock rule scale scalePositive depth resistanceScale kind (configuration depth) : ℝ) =
      (if kind = 2 then
        (Nat.card (ActualFiniteCluster rule configuration scale scalePositive depth) : ℝ)
        else 2 * Fintype.card (ClusterEdge (rule.generation depth).network (configuration depth))) *
      resistanceScale ^ (depth + 1) := by
  classical
  have same : Nat.card (ActualFiniteCluster rule (configurationAtDepth rule depth (configuration depth)) scale scalePositive depth) =
      Nat.card (ActualFiniteCluster rule configuration scale scalePositive depth) :=
    Nat.card_congr (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).toEquiv
  letI := clusterEdge_nonempty (rule.generation depth).network (configuration depth) crossing
  have verticesPositive : (0 : ℝ) < Nat.card (ActualFiniteCluster rule configuration scale scalePositive depth) :=
    Nat.cast_pos.mpr Nat.card_pos
  have edgesPositive : (0 : ℝ) < Fintype.card (ClusterEdge (rule.generation depth).network (configuration depth)) :=
    Nat.cast_pos.mpr Fintype.card_pos
  unfold actualFiniteAnnealedNaturalClock
  rw [Real.coe_toNNReal]
  · simp only [same, ← clusterEdge_card]
  · rw [same, ← clusterEdge_card]
    split_ifs <;> positivity

theorem actualFiniteAnnealedNaturalClock_positive
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (resistanceScale : ℝ) (resistancePositive : 0 < resistanceScale) (kind : Fin 3) :
    (0 : ℝ) < actualFiniteAnnealedNaturalClock rule scale scalePositive depth resistanceScale kind (configuration depth) := by
  rw [actualFiniteAnnealedNaturalClock_original_identity rule configuration scale scalePositive depth crossing resistanceScale resistancePositive kind]
  letI := clusterEdge_nonempty (rule.generation depth).network (configuration depth) crossing
  have verticesPositive : (0 : ℝ) < Nat.card (ActualFiniteCluster rule configuration scale scalePositive depth) :=
    Nat.cast_pos.mpr Nat.card_pos
  have edgesPositive : (0 : ℝ) < Fintype.card (ClusterEdge (rule.generation depth).network (configuration depth)) :=
    Nat.cast_pos.mpr Fintype.card_pos
  split_ifs <;> positivity

end
end IGSIII34.Spectral
