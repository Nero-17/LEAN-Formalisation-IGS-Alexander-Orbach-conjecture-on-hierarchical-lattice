import IGSIII.Geometry.MarkedComponentRadii
import Universality.Graph.GenerationCellEmbedding

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {vertices edges : ℕ}

def plantedVertex (network : FiniteNetwork vertices edges) (source_side : Bool) : Fin vertices :=
  if source_side then network.source else network.target

/-- The old rule vertices embedded in a true top-down generation. -/
noncomputable def oldVertexEmbedding (rule : Rule) (depth : ℕ) :
    Fin rule.vertices ↪ Fin (rule.generation (depth + 1)).vertices where
  toFun vertex := (rule.generationTopDecomposition depth).vertex.symm
    (Fintype.equivFin _ (Sum.inl vertex))
  inj' := (rule.generationTopDecomposition depth).vertex.symm.injective.comp
    ((Fintype.equivFin _).injective.comp Sum.inl_injective)

theorem oldVertexEmbedding_planted (rule : Rule) (depth : ℕ) (source_side : Bool) :
    oldVertexEmbedding rule depth (plantedVertex rule.network source_side) =
      plantedVertex (rule.generation (depth + 1)).network source_side := by
  apply (rule.generationTopDecomposition depth).vertex.injective
  change (rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm _) = _
  rw [Equiv.apply_symm_apply]
  cases source_side
  · exact (rule.generationTopDecomposition depth).target.symm
  · exact (rule.generationTopDecomposition depth).source.symm

theorem generationCellEmbedding_source (rule : Rule) (depth : ℕ) (edge : Fin rule.edges) :
    (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.source =
      oldVertexEmbedding rule depth (rule.network.endpoint edge).1 := by
  change (rule.generationTopDecomposition depth).vertex.symm
      (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge (rule.generation depth).network.source)) = _
  rw [rule.network.cellVertex_source]
  rfl

theorem generationCellEmbedding_target (rule : Rule) (depth : ℕ) (edge : Fin rule.edges) :
    (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.target =
      oldVertexEmbedding rule depth (rule.network.endpoint edge).2 := by
  change (rule.generationTopDecomposition depth).vertex.symm
      (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge (rule.generation depth).network.target)) = _
  rw [rule.network.cellVertex_target]
  rfl

/-- All vertices born by the specified top-down generation, inside an actual
finite descendant graph. The definition retains old junctions and every cell. -/
noncomputable def finiteSkeletonVertices (rule : Rule) :
    (depth : ℕ) → ℕ → Finset (Fin (rule.generation depth).vertices)
  | 0, _ => Finset.univ
  | depth + 1, 0 => Finset.univ.map (oldVertexEmbedding rule depth)
  | depth + 1, age + 1 => (Finset.univ.map (oldVertexEmbedding rule depth)) ∪
      Finset.univ.biUnion (fun edge => (finiteSkeletonVertices rule depth age).map
        (rule.generationCellEmbedding depth edge).vertex)

theorem oldVertex_mem_finiteSkeleton (rule : Rule) (depth age : ℕ) (vertex : Fin rule.vertices) :
    oldVertexEmbedding rule depth vertex ∈ finiteSkeletonVertices rule (depth + 1) age := by
  cases age with
  | zero => exact Finset.mem_map.mpr ⟨vertex, Finset.mem_univ _, rfl⟩
  | succ age => exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨vertex, Finset.mem_univ _, rfl⟩)

theorem childVertex_mem_finiteSkeleton (rule : Rule) (depth age : ℕ) (edge : Fin rule.edges)
    (vertex : Fin (rule.generation depth).vertices) (membership : vertex ∈ finiteSkeletonVertices rule depth age) :
    (rule.generationCellEmbedding depth edge).vertex vertex ∈ finiteSkeletonVertices rule (depth + 1) (age + 1) := by
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨edge, Finset.mem_univ _, Finset.mem_map.mpr ⟨vertex, membership, rfl⟩⟩)

theorem generationCellEmbedding_restrict_marked (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) (edge : Fin rule.edges) :
    (rule.generationCellEmbedding depth edge).restrict
      (markedGenerationConfiguration rule marks (depth + 1) address opened) =
      markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge) := by
  funext child
  change generationTopCells rule depth (markedGenerationConfiguration rule marks (depth + 1) address opened) edge child = _
  rw [markedGenerationConfiguration_topCells]

noncomputable def markedChildHom (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) (edge : Fin rule.edges) :
    (rule.generation depth).network.openGraph
        (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge)) →g
      (rule.generation (depth + 1)).network.openGraph (markedGenerationConfiguration rule marks (depth + 1) address opened) where
  toFun := (rule.generationCellEmbedding depth edge).vertex
  map_rel' := by
    intro first last adjacent
    apply ((rule.generationCellEmbedding depth edge).openGraphHom
      (markedGenerationConfiguration rule marks (depth + 1) address opened)).map_rel
    rwa [generationCellEmbedding_restrict_marked]

theorem markedChildHom_vertex (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) (edge : Fin rule.edges)
    (vertex : Fin (rule.generation depth).vertices) :
    markedChildHom rule marks depth address opened edge vertex =
      (rule.generationCellEmbedding depth edge).vertex vertex := by
  rfl

theorem markedChild_distance_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) (edge : Fin rule.edges)
    (first last : Fin (rule.generation depth).vertices)
    (reachable : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).Reachable first last) :
    ((rule.generation (depth + 1)).network.openGraph (markedGenerationConfiguration rule marks (depth + 1) address opened)).dist
      ((rule.generationCellEmbedding depth edge).vertex first) ((rule.generationCellEmbedding depth edge).vertex last) ≤
    ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).dist first last := by
  obtain ⟨walk, length⟩ := reachable.exists_walk_length_eq_dist
  have bound := SimpleGraph.dist_le (walk.map (markedChildHom rule marks depth address opened edge))
  simpa only [markedChildHom_vertex, SimpleGraph.Walk.length_map, length] using bound

theorem generationVertex_old_or_child (rule : Rule) (depth : ℕ)
    (vertex : Fin (rule.generation (depth + 1)).vertices) :
    (∃ old, vertex = oldVertexEmbedding rule depth old) ∨
      (∃ edge child, vertex = (rule.generationCellEmbedding depth edge).vertex child) := by
  obtain ⟨point, point_identity⟩ := (Fintype.equivFin
    (rule.network.SubstitutionVertex (rule.generation depth).network)).surjective
      ((rule.generationTopDecomposition depth).vertex vertex)
  cases point with
  | inl old =>
    left
    refine ⟨old, ?_⟩
    apply (rule.generationTopDecomposition depth).vertex.injective
    change _ = (rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm _)
    rw [Equiv.apply_symm_apply]
    exact point_identity.symm
  | inr pair =>
    rcases pair with ⟨edge, inside⟩
    right
    refine ⟨edge, inside.val, ?_⟩
    apply (rule.generationTopDecomposition depth).vertex.injective
    change _ = (rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm
        (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge inside.val)))
    rw [Equiv.apply_symm_apply]
    have cell_identity : rule.network.cellVertex (rule.generation depth).network edge inside.val = Sum.inr (edge, inside) := by
      simp only [cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
      rfl
    rw [cell_identity]
    exact point_identity.symm

theorem finiteSkeletonVertices_self (rule : Rule) (depth : ℕ) :
    finiteSkeletonVertices rule depth depth = Finset.univ := by
  induction depth with
  | zero => rfl
  | succ depth induction_hypothesis =>
    apply Finset.eq_univ_of_forall
    intro vertex
    rcases generationVertex_old_or_child rule depth vertex with ⟨old, rfl⟩ | ⟨edge, child, rfl⟩
    · exact oldVertex_mem_finiteSkeleton rule depth (depth + 1) old
    · exact childVertex_mem_finiteSkeleton rule depth depth edge child
        (by rw [induction_hypothesis]; exact Finset.mem_univ _)

/-- A retained point is old, or lies in an actual child component whose
available terminal is itself retained in the parent component. -/
theorem retained_generation_point_old_or_child (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened source_side : Bool)
    (vertex : Fin (rule.generation (depth + 1)).vertices)
    (reachable : ((rule.generation (depth + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (depth + 1) address opened)).Reachable
        (plantedVertex (rule.generation (depth + 1)).network source_side) vertex) :
    (∃ old, vertex = oldVertexEmbedding rule depth old) ∨
      ∃ (edge : Fin rule.edges) (child : Fin (rule.generation depth).vertices) (child_side : Bool),
        vertex = (rule.generationCellEmbedding depth edge).vertex child ∧
        ((rule.generation depth).network.openGraph
          (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).Reachable
            (plantedVertex (rule.generation depth).network child_side) child ∧
        ((rule.generation (depth + 1)).network.openGraph
          (markedGenerationConfiguration rule marks (depth + 1) address opened)).Reachable
            (plantedVertex (rule.generation (depth + 1)).network source_side)
            ((rule.generationCellEmbedding depth edge).vertex (plantedVertex (rule.generation depth).network child_side)) := by
  have transported := reachable.map ((rule.generationTopDecomposition depth).openGraphIso
    (markedGenerationConfiguration rule marks (depth + 1) address opened)).toHom
  have mapped_configuration : (rule.generationTopDecomposition depth).configuration
      (markedGenerationConfiguration rule marks (depth + 1) address opened) =
      substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks depth
        (address ++ [edge]) (marks (address, opened) edge)) := by
    simp only [markedGenerationConfiguration, Equiv.apply_symm_apply]
  change ((rule.network.substitute (rule.generation depth).network).openGraph
    ((rule.generationTopDecomposition depth).configuration
      (markedGenerationConfiguration rule marks (depth + 1) address opened))).Reachable
        ((rule.generationTopDecomposition depth).vertex (plantedVertex (rule.generation (depth + 1)).network source_side))
        ((rule.generationTopDecomposition depth).vertex vertex) at transported
  rw [mapped_configuration] at transported
  have root_identity : (rule.generationTopDecomposition depth).vertex
      (plantedVertex (rule.generation (depth + 1)).network source_side) =
      Fintype.equivFin (rule.network.SubstitutionVertex (rule.generation depth).network)
        (Sum.inl (plantedVertex rule.network source_side)) := by
    rw [← oldVertexEmbedding_planted rule depth source_side]
    exact Equiv.apply_symm_apply _ _
  rw [root_identity] at transported
  obtain ⟨point, point_identity⟩ := (Fintype.equivFin
    (rule.network.SubstitutionVertex (rule.generation depth).network)).surjective
      ((rule.generationTopDecomposition depth).vertex vertex)
  rw [← point_identity, rule.network.substitute_reachable_iff,
    rule.network.substitutedReachable_iff_active] at transported
  cases point with
  | inl old =>
    left
    refine ⟨old, ?_⟩
    apply (rule.generationTopDecomposition depth).vertex.injective
    change _ = (rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm _)
    rw [Equiv.apply_symm_apply]
    exact point_identity.symm
  | inr pair =>
    rcases pair with ⟨edge, inside⟩
    have vertex_identity : vertex = (rule.generationCellEmbedding depth edge).vertex inside.val := by
      apply (rule.generationTopDecomposition depth).vertex.injective
      change _ = (rule.generationTopDecomposition depth).vertex
        ((rule.generationTopDecomposition depth).vertex.symm
          (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge inside.val)))
      rw [Equiv.apply_symm_apply]
      have cell_identity : rule.network.cellVertex (rule.generation depth).network edge inside.val = Sum.inr (edge, inside) := by
        simp only [cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
        rfl
      rw [cell_identity]
      exact point_identity.symm
    change (_ ∧ ((rule.generation depth).network.openGraph
        (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).Reachable
          (rule.generation depth).network.source inside.val) ∨
      (_ ∧ ((rule.generation depth).network.openGraph
        (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).Reachable
          (rule.generation depth).network.target inside.val) at transported
    right
    rcases transported with ⟨_, child_reachable⟩ | ⟨_, child_reachable⟩
    · refine ⟨edge, inside.val, true, vertex_identity, child_reachable, ?_⟩
      have mapped := child_reachable.map (markedChildHom rule marks depth address opened edge)
      simp only [markedChildHom_vertex] at mapped
      rw [← vertex_identity] at mapped
      exact reachable.trans mapped.symm
    · refine ⟨edge, inside.val, false, vertex_identity, child_reachable, ?_⟩
      have mapped := child_reachable.map (markedChildHom rule marks depth address opened edge)
      simp only [markedChildHom_vertex] at mapped
      rw [← vertex_identity] at mapped
      exact reachable.trans mapped.symm

end IGSIII.Geometry
