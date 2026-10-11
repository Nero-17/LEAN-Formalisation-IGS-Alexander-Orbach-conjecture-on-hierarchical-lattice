import IGSIII34.ResistanceLimit.HarmonicTower
import IGSIII34.ResistanceLimit.CompletionLocality

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry

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

variable (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
variable (restriction : ∀ depth (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)),
  potentials (depth + 1) (rule.generationOldVertex depth vertex.val) = potentials depth vertex.val)

include restriction

theorem coherentPotential_persistent (first last : ℕ) (bound : first ≤ last)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    potentials last (retainedPersistentVertexEmbedding rule configuration coherent first last bound vertex).val =
      potentials first vertex.val := by
  induction last, bound using Nat.le_induction with
  | base => simp only [retainedPersistentVertexEmbedding_val, persistentVertexEmbedding,
      Universality.Geometry.IsometricSequence.transition, Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ last bound previous =>
    rw [retainedPersistentVertexEmbedding_val,
      ← persistentVertexEmbedding_trans rule first last (last + 1) bound (Nat.le_succ last),
      persistentVertexEmbedding_next]
    exact (restriction last (retainedPersistentVertexEmbedding rule configuration coherent first last bound vertex)).trans previous

theorem coherentPotential_transition (first last : ℕ) (bound : first ≤ last)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    potentials first vertex.val = potentials last
      (Universality.Geometry.IsometricSequence.transition
        (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
        (retainedOldVertexEmbedding rule configuration coherent) first last bound vertex).val := by
  rw [retainedTransition_val]
  exact (coherentPotential_persistent rule configuration coherent potentials restriction first last bound vertex).symm

/-- Every coherent finite potential family defines an actual function on the
retained skeleton. Harmonicity is not required. -/
def coherentSkeletonPotential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ :=
  DirectLimit.lift (Universality.Geometry.IsometricSequence.transition
    (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (retainedOldVertexEmbedding rule configuration coherent))
    (fun depth vertex => potentials depth vertex.val)
    (coherentPotential_transition rule configuration coherent potentials restriction)

theorem coherentSkeletonPotential_retained (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    coherentSkeletonPotential rule configuration coherent resistance positive compatible potentials restriction
      (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex) =
        potentials depth vertex.val := rfl

theorem coherentSkeletonPotential_trace_energy (depth : ℕ) :
    traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) depth
      (coherentSkeletonPotential rule configuration coherent resistance positive compatible potentials restriction) =
      sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth) (potentials depth) := by
  rw [skeleton_traceEnergy_eq_source_energy]
  apply sourceComponentEnergy_congr_retained
  intro vertex retained
  have retained' : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source vertex := by
    rwa [graph_eq_openGraph] at retained
  rw [electricalSkeletonPoint_retained rule configuration coherent resistance positive compatible depth ⟨vertex, retained'⟩]
  exact coherentSkeletonPotential_retained rule configuration coherent resistance positive compatible potentials restriction depth ⟨vertex, retained'⟩

theorem coherentSkeletonPotential_finite_iff :
    coherentSkeletonPotential rule configuration coherent resistance positive compatible potentials restriction ∈
      energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance)
        (skeletonEnergyConductance_nonnegative rule configuration resistance positive) ↔
    BddAbove (Set.range (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (configuration depth)) (resistance depth) (potentials depth))) := by
  change BddAbove (Set.range _) ↔ _
  simp only [coherentSkeletonPotential_trace_energy]

theorem coherentSkeletonPotential_limiting_energy :
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (coherentSkeletonPotential rule configuration coherent resistance positive compatible potentials restriction) =
      ⨆ depth, sourceComponentEnergy (network (rule.generation depth).network (configuration depth))
        (resistance depth) (potentials depth) := by
  unfold limitingEnergy
  simp only [coherentSkeletonPotential_trace_energy]

end
end IGSIII34.Forms
