import IGSIII.Geometry.ActualSkeletonMetric
import IGSIII.Geometry.ActualSkeletonVertices
import IGSIII.Chemical.SubstitutionPaths.CommonPrefix
import Universality.Geometry.PercolationClusterVertices
import Universality.Geometry.GenerationCellMetric

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

/-- The persistent coarse vertices in the actual block decomposition. -/
noncomputable def blockOldVertexEmbedding (rule : Rule) (coarse fine : ℕ) :
    Fin (rule.generation coarse).vertices ↪ Fin (rule.generation (coarse + fine + 1)).vertices where
  toFun vertex := (rule.generationBlockDecomposition coarse fine).vertex.symm
    (Fintype.equivFin ((rule.generation coarse).network.SubstitutionVertex (rule.generation fine).network)
      (Sum.inl vertex))
  inj' := (rule.generationBlockDecomposition coarse fine).vertex.symm.injective.comp
    ((Fintype.equivFin _).injective.comp Sum.inl_injective)

theorem blockOldVertexEmbedding_zero (rule : Rule) (coarse : ℕ)
    (vertex : Fin (rule.generation coarse).vertices) :
    blockOldVertexEmbedding rule coarse 0 vertex = rule.generationOldVertex coarse vertex := rfl

theorem blockOldVertexEmbedding_next (rule : Rule) (coarse fine : ℕ)
    (vertex : Fin (rule.generation coarse).vertices) :
    rule.generationOldVertex (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex) =
      blockOldVertexEmbedding rule coarse (fine + 1) vertex := by
  apply (rule.generationBlockDecomposition coarse (fine + 1)).vertex.injective
  change (rule.generation coarse).network.substitutionAssociatorVertex (rule.generation fine).network rule.network
    (((rule.generationBlockDecomposition coarse fine).substitute (NetworkEquivalence.refl rule.network)).vertex
      (rule.generationOldVertex (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex))) = _
  rw [show (((rule.generationBlockDecomposition coarse fine).substitute (NetworkEquivalence.refl rule.network)).vertex
      (rule.generationOldVertex (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex))) =
      Fintype.equivFin _ (Sum.inl ((rule.generationBlockDecomposition coarse fine).vertex
        (blockOldVertexEmbedding rule coarse fine vertex))) from
    (rule.generationBlockDecomposition coarse fine).substituteVertex_old (NetworkEquivalence.refl rule.network) _]
  change (rule.generation coarse).network.substitutionAssociatorVertex (rule.generation fine).network rule.network
      (Fintype.equivFin _ (Sum.inl ((rule.generationBlockDecomposition coarse fine).vertex
        ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ (Sum.inl vertex)))))) =
    (rule.generationBlockDecomposition coarse (fine + 1)).vertex
      ((rule.generationBlockDecomposition coarse (fine + 1)).vertex.symm (Fintype.equivFin _ (Sum.inl vertex)))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (rule.generation coarse).network.substitutionAssociatorVertex_old (rule.generation fine).network rule.network vertex

noncomputable def persistentVertexEmbedding (rule : Rule) (first second : ℕ) (bound : first ≤ second) :
    Fin (rule.generation first).vertices ↪ Fin (rule.generation second).vertices :=
  Universality.Geometry.IsometricSequence.transition (fun depth => Fin (rule.generation depth).vertices)
    rule.generationOldVertex first second bound

theorem blockOldVertexEmbedding_eq_persistent (rule : Rule) (coarse fine : ℕ)
    (vertex : Fin (rule.generation coarse).vertices) :
    blockOldVertexEmbedding rule coarse fine vertex =
      persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) vertex := by
  induction fine with
  | zero =>
    simp only [blockOldVertexEmbedding_zero, persistentVertexEmbedding,
      Universality.Geometry.IsometricSequence.transition, Function.Embedding.coeFn_mk, Nat.add_zero,
      Nat.leRecOn_succ']
  | succ fine induction_hypothesis =>
    rw [← blockOldVertexEmbedding_next, induction_hypothesis]
    change _ = Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
      (show coarse ≤ (coarse + fine + 1) + 1 by omega) (fun {depth} => rule.generationOldVertex depth) vertex
    rw [Nat.leRecOn_succ (show coarse ≤ coarse + fine + 1 by omega)]
    rfl

theorem persistentVertexEmbedding_trans (rule : Rule) (first second third : ℕ)
    (first_bound : first ≤ second) (second_bound : second ≤ third)
    (vertex : Fin (rule.generation first).vertices) :
    persistentVertexEmbedding rule second third second_bound
        (persistentVertexEmbedding rule first second first_bound vertex) =
      persistentVertexEmbedding rule first third (first_bound.trans second_bound) vertex := by
  unfold persistentVertexEmbedding Universality.Geometry.IsometricSequence.transition
  exact (Nat.leRecOn_trans (C := fun depth => Fin (rule.generation depth).vertices)
    (next := fun {depth} => rule.generationOldVertex depth) first_bound second_bound vertex).symm

theorem blockOldVertexEmbedding_planted (rule : Rule) (coarse fine : ℕ) (source_side : Bool) :
    blockOldVertexEmbedding rule coarse fine (plantedVertex (rule.generation coarse).network source_side) =
      plantedVertex (rule.generation (coarse + fine + 1)).network source_side := by
  apply (rule.generationBlockDecomposition coarse fine).vertex.injective
  change (rule.generationBlockDecomposition coarse fine).vertex
      ((rule.generationBlockDecomposition coarse fine).vertex.symm _) = _
  rw [Equiv.apply_symm_apply]
  cases source_side
  · exact (rule.generationBlockDecomposition coarse fine).target.symm
  · exact (rule.generationBlockDecomposition coarse fine).source.symm

theorem blockOldVertexEmbedding_reachable_iff (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (first last : Fin (rule.generation coarse).vertices) :
    ((rule.generation (coarse + fine + 1)).network.openGraph configuration).Reachable
        (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last) ↔
      ((rule.generation coarse).network.openGraph (generationBlockCoarse rule coarse fine configuration)).Reachable first last := by
  have transported := (((rule.generationBlockDecomposition coarse fine).openGraphIso configuration).reachable_iff
    (u := blockOldVertexEmbedding rule coarse fine first) (v := blockOldVertexEmbedding rule coarse fine last)).symm
  change _ ↔ (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
      ((rule.generationBlockDecomposition coarse fine).configuration configuration)).Reachable
        ((rule.generationBlockDecomposition coarse fine).vertex (blockOldVertexEmbedding rule coarse fine first))
        ((rule.generationBlockDecomposition coarse fine).vertex (blockOldVertexEmbedding rule coarse fine last)) at transported
  have configuration_identity : (rule.generationBlockDecomposition coarse fine).configuration configuration =
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  rw [configuration_identity] at transported
  simp only [blockOldVertexEmbedding, Function.Embedding.coeFn_mk, Equiv.apply_symm_apply] at transported
  exact transported.trans (((rule.generation coarse).network.substitute_reachable_iff (rule.generation fine).network _ _ _).trans
    ((rule.generation coarse).network.substitutedReachable_iff (rule.generation fine).network _ first last))

theorem generationOldVertex_planted (rule : Rule) (depth : ℕ) (source_side : Bool) :
    rule.generationOldVertex depth (plantedVertex (rule.generation depth).network source_side) =
      plantedVertex (rule.generation (depth + 1)).network source_side := by
  cases source_side <;> rfl

theorem persistentVertexEmbedding_planted (rule : Rule) (first second : ℕ) (bound : first ≤ second)
    (source_side : Bool) :
    persistentVertexEmbedding rule first second bound (plantedVertex (rule.generation first).network source_side) =
      plantedVertex (rule.generation second).network source_side := by
  induction second, bound using Nat.le_induction with
  | base =>
    simp only [persistentVertexEmbedding, Universality.Geometry.IsometricSequence.transition,
      Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ second bound induction_hypothesis =>
    change Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
      (show first ≤ second + 1 by omega) (fun {depth} => rule.generationOldVertex depth)
      (plantedVertex (rule.generation first).network source_side) = _
    rw [Nat.leRecOn_succ bound]
    change rule.generationOldVertex second
      (persistentVertexEmbedding rule first second bound (plantedVertex (rule.generation first).network source_side)) = _
    rw [induction_hypothesis, generationOldVertex_planted]

theorem persistentVertexEmbedding_reachable_iff (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (first second : ℕ) (bound : first ≤ second) (source target : Fin (rule.generation first).vertices) :
    ((rule.generation second).network.openGraph (configuration second)).Reachable
        (persistentVertexEmbedding rule first second bound source) (persistentVertexEmbedding rule first second bound target) ↔
      ((rule.generation first).network.openGraph (configuration first)).Reachable source target := by
  induction second, bound using Nat.le_induction with
  | base =>
    simp only [persistentVertexEmbedding, Universality.Geometry.IsometricSequence.transition,
      Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ second bound induction_hypothesis =>
    change ((rule.generation (second + 1)).network.openGraph (configuration (second + 1))).Reachable
      (Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
        (show first ≤ second + 1 by omega) (fun {depth} => rule.generationOldVertex depth) source)
      (Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
        (show first ≤ second + 1 by omega) (fun {depth} => rule.generationOldVertex depth) target) ↔ _
    rw [Nat.leRecOn_succ bound, Nat.leRecOn_succ bound, rule.generation_reachable_old_iff, coherent second]
    exact induction_hypothesis

end IGSIII.Geometry
