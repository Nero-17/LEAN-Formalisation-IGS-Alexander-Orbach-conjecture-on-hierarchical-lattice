import IGSIII.Geometry.ActualSkeletonNets
import IGSIII.Geometry.ActualSkeletonPersistence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem oldVertexEmbedding_next (rule : Rule) (depth : ℕ) (vertex : Fin rule.vertices) :
    rule.generationOldVertex (depth + 1) (oldVertexEmbedding rule depth vertex) =
      oldVertexEmbedding rule (depth + 1) vertex := by
  apply (rule.generationTopDecomposition (depth + 1)).vertex.injective
  change rule.network.substitutionAssociatorVertex (rule.generation depth).network rule.network
    (((rule.generationTopDecomposition depth).substitute (NetworkEquivalence.refl rule.network)).vertex
      (rule.generationOldVertex (depth + 1) (oldVertexEmbedding rule depth vertex))) = _
  rw [show (((rule.generationTopDecomposition depth).substitute (NetworkEquivalence.refl rule.network)).vertex
      (rule.generationOldVertex (depth + 1) (oldVertexEmbedding rule depth vertex))) =
      Fintype.equivFin _ (Sum.inl ((rule.generationTopDecomposition depth).vertex
        (oldVertexEmbedding rule depth vertex))) from
    (rule.generationTopDecomposition depth).substituteVertex_old (NetworkEquivalence.refl rule.network) _]
  change rule.network.substitutionAssociatorVertex (rule.generation depth).network rule.network
      (Fintype.equivFin _ (Sum.inl ((rule.generationTopDecomposition depth).vertex
        ((rule.generationTopDecomposition depth).vertex.symm (Fintype.equivFin _ (Sum.inl vertex)))))) =
    (rule.generationTopDecomposition (depth + 1)).vertex
      ((rule.generationTopDecomposition (depth + 1)).vertex.symm (Fintype.equivFin _ (Sum.inl vertex)))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact rule.network.substitutionAssociatorVertex_old (rule.generation depth).network rule.network vertex

theorem finset_map_biUnion {First Second Index : Type*} [DecidableEq First] [DecidableEq Second]
    (indices : Finset Index) (sets : Index → Finset First) (embedding : First ↪ Second) :
    (indices.biUnion sets).map embedding = indices.biUnion (fun index => (sets index).map embedding) := by
  ext point
  simp only [Finset.mem_map, Finset.mem_biUnion]
  aesop

/-- Persisting the preceding actual birth skeleton produces exactly the same
birth skeleton inside the next microscopic graph. -/
theorem finiteSkeletonVertices_next (rule : Rule) (depth age : ℕ) (bound : age ≤ depth) :
    (finiteSkeletonVertices rule depth age).map (rule.generationOldVertex depth) =
      finiteSkeletonVertices rule (depth + 1) age := by
  induction depth generalizing age with
  | zero =>
    have age_zero : age = 0 := by omega
    subst age
    rfl
  | succ depth induction_hypothesis =>
    have old_image : (Finset.univ.map (oldVertexEmbedding rule depth)).map (rule.generationOldVertex (depth + 1)) =
        Finset.univ.map (oldVertexEmbedding rule (depth + 1)) := by
      rw [Finset.map_map]
      congr 1
      apply Function.Embedding.ext
      intro vertex
      exact oldVertexEmbedding_next rule depth vertex
    cases age with
    | zero => exact old_image
    | succ age =>
      have child_image (edge : Fin rule.edges) :
          ((finiteSkeletonVertices rule depth age).map (rule.generationCellEmbedding depth edge).vertex).map
            (rule.generationOldVertex (depth + 1)) =
          (finiteSkeletonVertices rule (depth + 1) age).map (rule.generationCellEmbedding (depth + 1) edge).vertex := by
        rw [← induction_hypothesis age (by omega), Finset.map_map, Finset.map_map]
        congr 1
        apply Function.Embedding.ext
        intro vertex
        exact rule.generationCellEmbedding_oldVertex depth edge vertex
      change ((Finset.univ.map (oldVertexEmbedding rule depth)) ∪
          Finset.univ.biUnion (fun edge => (finiteSkeletonVertices rule depth age).map
            (rule.generationCellEmbedding depth edge).vertex)).map (rule.generationOldVertex (depth + 1)) = _
      rw [Finset.map_union, old_image, finset_map_biUnion]
      simp_rw [child_image]
      rfl

theorem finiteSkeletonVertices_eq_persistent_image (rule : Rule) (age depth : ℕ) (bound : age ≤ depth) :
    finiteSkeletonVertices rule depth age = Finset.univ.map (persistentVertexEmbedding rule age depth bound) := by
  induction depth, bound using Nat.le_induction with
  | base =>
    rw [finiteSkeletonVertices_self]
    have identity : persistentVertexEmbedding rule age age le_rfl = Function.Embedding.refl _ := by
      apply Function.Embedding.ext
      intro vertex
      change Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices) le_rfl
        (fun {depth} => rule.generationOldVertex depth) vertex = vertex
      exact Nat.leRecOn_self (C := fun depth => Fin (rule.generation depth).vertices)
        (next := fun {depth} => rule.generationOldVertex depth) vertex
    rw [identity]
    exact Finset.map_refl.symm
  | succ depth bound induction_hypothesis =>
    rw [← finiteSkeletonVertices_next rule depth age bound, induction_hypothesis, Finset.map_map]
    congr 1
    apply Function.Embedding.ext
    intro vertex
    change rule.generationOldVertex depth
        (Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices) bound
          (fun {depth} => rule.generationOldVertex depth) vertex) = _
    exact (Nat.leRecOn_succ (C := fun depth => Fin (rule.generation depth).vertices)
      (next := fun {depth} => rule.generationOldVertex depth) bound vertex).symm

end IGSIII.Geometry
