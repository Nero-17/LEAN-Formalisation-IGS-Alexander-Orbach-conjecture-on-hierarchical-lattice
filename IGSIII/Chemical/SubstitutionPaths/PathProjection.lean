import IGSIII.Chemical.SubstitutionPaths.IndexedPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Actual pathwise facts for hierarchical terminal-path encoding

These lemmas concern the actual glued substitution graph. Interior walk
segments stay inside one child, they can meet an old vertex only at a child
terminal, and a simple microscopic path sees each old vertex at most once.
The complete ordered segmentation and the resulting exponential path-count
bound remain separate obligations; neither is assumed here.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

theorem substitutedGraph_adj_interior_same_cell
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (first second : Fin outerEdges) (firstInterior secondInterior : inner.InteriorVertex)
    (adjacent : (outer.substitutedGraph inner configuration).Adj
      (Sum.inr (first, firstInterior)) (Sum.inr (second, secondInterior))) : first = second := by
  obtain ⟨_, cell, source, target, _, firstEndpoint, secondEndpoint⟩ := adjacent
  have firstCell := (outer.cellVertex_eq_interior_iff inner cell first source firstInterior).mp firstEndpoint
  have secondCell := (outer.cellVertex_eq_interior_iff inner cell second target secondInterior).mp secondEndpoint
  exact firstCell.1.symm.trans secondCell.1

theorem cellVertex_eq_old_imp_endpoint
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (edge : Fin outerEdges) (inside : Fin innerVertices) (old : Fin outerVertices)
    (equality : outer.cellVertex inner edge inside = Sum.inl old) :
    old = (outer.endpoint edge).1 ∨ old = (outer.endpoint edge).2 := by
  by_cases atSource : inside = inner.source
  · subst inside
    rw [outer.cellVertex_source] at equality
    exact Or.inl (Sum.inl.inj equality).symm
  · by_cases atTarget : inside = inner.target
    · subst inside
      rw [outer.cellVertex_target] at equality
      exact Or.inr (Sum.inl.inj equality).symm
    · simp only [FiniteNetwork.cellVertex, dif_neg atSource, dif_neg atTarget] at equality
      contradiction

theorem substitutedGraph_old_interior_endpoint
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (old : Fin outerVertices) (edge : Fin outerEdges) (inside : inner.InteriorVertex)
    (adjacent : (outer.substitutedGraph inner configuration).Adj (Sum.inl old) (Sum.inr (edge, inside))) :
    old = (outer.endpoint edge).1 ∨ old = (outer.endpoint edge).2 := by
  obtain ⟨_, cell, source, target, _, oldEndpoint, insideEndpoint⟩ := adjacent
  have same := (outer.cellVertex_eq_interior_iff inner cell edge target inside).mp insideEndpoint
  rw [same.1] at oldEndpoint
  exact cellVertex_eq_old_imp_endpoint outer inner edge source old oldEndpoint

theorem interior_walk_stays_in_cell
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    {first last : outer.SubstitutionVertex inner}
    (walk : (outer.substitutedGraph inner configuration).Walk first last) (edge : Fin outerEdges)
    (firstInside : ∃ inside : inner.InteriorVertex, first = Sum.inr (edge, inside))
    (noOldVertices : ∀ vertex ∈ walk.support,
      ∃ cell : Fin outerEdges, ∃ inside : inner.InteriorVertex, vertex = Sum.inr (cell, inside)) :
    ∃ inside : inner.InteriorVertex, last = Sum.inr (edge, inside) := by
  induction walk generalizing edge with
  | nil => exact firstInside
  | @cons first next last adjacent tail inductionHypothesis =>
      obtain ⟨firstInterior, rfl⟩ := firstInside
      obtain ⟨nextCell, nextInterior, nextEquality⟩ := noOldVertices next (by simp)
      have same : edge = nextCell := substitutedGraph_adj_interior_same_cell outer inner configuration
        edge nextCell firstInterior nextInterior (by simpa only [nextEquality] using adjacent)
      apply inductionHypothesis edge
      · exact ⟨nextInterior, by rw [nextEquality, same]⟩
      · intro vertex membership
        exact noOldVertices vertex (by simp [membership])

def oldVertexProjection {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges) :
    outer.SubstitutionVertex inner → Option (Fin outerVertices)
  | Sum.inl vertex => some vertex
  | Sum.inr _ => none

theorem simple_walk_old_vertices_nodup
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    {source target : outer.SubstitutionVertex inner}
    (walk : (outer.substitutedGraph inner configuration).Walk source target) (simple : walk.IsPath) :
    (walk.support.filterMap (oldVertexProjection outer inner)).Nodup := by
  apply List.Nodup.filterMap _ simple.support_nodup
  intro first second old firstMembership secondMembership
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          simp only [oldVertexProjection, Option.mem_some_iff] at firstMembership secondMembership
          exact congrArg Sum.inl (firstMembership.trans secondMembership.symm)
      | inr second => simp only [oldVertexProjection, Option.not_mem_none] at secondMembership
  | inr first => simp only [oldVertexProjection, Option.not_mem_none] at firstMembership

end IGSIII.Chemical.Substitution
