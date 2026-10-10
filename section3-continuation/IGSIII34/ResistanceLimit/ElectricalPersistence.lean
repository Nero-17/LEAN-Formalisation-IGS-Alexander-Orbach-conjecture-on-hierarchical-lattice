import IGSIII34.ResistanceLimit.ActualSkeletonLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

def persistentNormalizedResistance (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (coarse : ℕ) (first last : Fin (rule.generation coarse).vertices) (depth : ℕ) : ℝ :=
  if bound : coarse ≤ depth then
    pairResistance (network (rule.generation depth).network (configuration depth)) (fun _ => 1)
      (persistentVertexEmbedding rule coarse depth bound first)
      (persistentVertexEmbedding rule coarse depth bound last) / scale ^ (depth + 1)
  else 0

theorem actual_persistent_skeleton_resistances_tendsto (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldNonnegative : ∀ address, 0 ≤ field address)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ) {first last : Fin (rule.generation coarse).vertices}
    (reachable : ((rule.generation coarse).network.openGraph (stationaryConfiguration rule marks coarse)).Reachable first last) :
    Tendsto (persistentNormalizedResistance rule (stationaryConfiguration rule marks) growth coarse first last) atTop
      (𝓝 (pairResistance (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
        (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val) first last)) := by
  apply (tendsto_add_atTop_iff_nat (coarse + 1)).mp
  apply (actual_marked_skeleton_resistances_tendsto rule marks crossing growth growthPositive
    field fieldNonnegative fieldLimit coarse reachable).congr'
  apply Eventually.of_forall
  intro fine
  dsimp only
  rw [show fine + (coarse + 1) = coarse + fine + 1 by omega]
  simp only [persistentNormalizedResistance, dif_pos (show coarse ≤ coarse + fine + 1 by omega)]
  rw [← blockOldVertexEmbedding_eq_persistent rule coarse fine first,
    ← blockOldVertexEmbedding_eq_persistent rule coarse fine last]
  simp only [div_eq_mul_inv, mul_comm, Nat.add_assoc]

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)

theorem electricalVertex_persistent (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    electricalVertex rule configuration coherent resistance positive compatible first vertex =
      electricalVertex rule configuration coherent resistance positive compatible second
        (retainedPersistentVertexEmbedding rule configuration coherent first second bound vertex) := by
  apply congrArg (fun point : ElectricalSkeleton rule configuration coherent resistance positive compatible =>
    UniformSpace.Completion.coe' point)
  rw [retainedPersistentVertexEmbedding_eq_transition]
  exact (DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) first second vertex bound).symm

end
end IGSIII34.ResistanceLimit
