import IGSIII.Chemical.BoundaryDistance
import Universality.Graph.SubstitutionPotential

/-!
# Localisation estimates in actual percolated cells

These estimates retain arbitrary noncrossing configurations and their
one-sided components. A signed boundary-distance potential forces a path
between distinct cells to pay both intrinsic boundary distances.
-/

set_option autoImplicit false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges)
    (inner : FiniteNetwork innerVertices innerEdges)

noncomputable def openCellBoundaryPotential
    (configuration : Fin outerEdges → Configuration innerEdges)
    (weight : Fin outerEdges → ℝ) : outer.SubstitutionVertex inner → ℝ :=
  outer.substitutionPotential inner (fun _ => 0) (fun edge point =>
    weight edge * componentBoundaryDistance (inner.openGraph (configuration edge))
      inner.source inner.target point)

@[simp] theorem openCellBoundaryPotential_cell
    (configuration : Fin outerEdges → Configuration innerEdges)
    (weight : Fin outerEdges → ℝ) (edge : Fin outerEdges) (point : Fin innerVertices) :
    openCellBoundaryPotential outer inner configuration weight (outer.cellVertex inner edge point) =
      weight edge * componentBoundaryDistance (inner.openGraph (configuration edge))
        inner.source inner.target point := by
  apply outer.substitutionPotential_cell inner (fun _ => 0)
  · intro edge
    simp
  · intro edge
    simp

@[simp] theorem openCellBoundaryPotential_old
    (configuration : Fin outerEdges → Configuration innerEdges)
    (weight : Fin outerEdges → ℝ) (point : Fin outerVertices) :
    openCellBoundaryPotential outer inner configuration weight (Sum.inl point) = 0 := rfl

theorem openCellBoundaryPotential_adj
    (configuration : Fin outerEdges → Configuration innerEdges)
    (weight : Fin outerEdges → ℝ) (bounded : ∀ edge, |weight edge| ≤ 1)
    {first second : outer.SubstitutionVertex inner}
    (adjacent : (outer.substitutedGraph inner configuration).Adj first second) :
    |openCellBoundaryPotential outer inner configuration weight first -
      openCellBoundaryPotential outer inner configuration weight second| ≤ 1 := by
  obtain ⟨_, edge, left, right, localAdjacent, rfl, rfl⟩ := adjacent
  rw [openCellBoundaryPotential_cell, openCellBoundaryPotential_cell, ← mul_sub, abs_mul]
  exact (mul_le_mul (bounded edge)
    (componentBoundaryDistance_adj _ inner.source inner.target localAdjacent)
    (abs_nonneg _) zero_le_one).trans (by norm_num)

theorem openCellBoundaryPotential_distance
    (configuration : Fin outerEdges → Configuration innerEdges)
    (weight : Fin outerEdges → ℝ) (bounded : ∀ edge, |weight edge| ≤ 1)
    {first second : outer.SubstitutionVertex inner}
    (reachable : (outer.substitutedGraph inner configuration).Reachable first second) :
    |openCellBoundaryPotential outer inner configuration weight first -
      openCellBoundaryPotential outer inner configuration weight second| ≤
      ((outer.substitutedGraph inner configuration).dist first second : ℝ) :=
  graph_height_distance_bound _ _
    (openCellBoundaryPotential_adj outer inner configuration weight bounded) reachable

theorem open_cell_boundary_le_distance_to_old
    (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (point : Fin innerVertices) (old : Fin outerVertices)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner edge point) (Sum.inl old)) :
    componentBoundaryDistance (inner.openGraph (configuration edge)) inner.source inner.target point ≤
      ((outer.substitutedGraph inner configuration).dist
        (outer.cellVertex inner edge point) (Sum.inl old) : ℝ) := by
  have bound := openCellBoundaryPotential_distance outer inner configuration (fun _ => 1)
    (fun _ => by norm_num) reachable
  simpa only [openCellBoundaryPotential_cell, openCellBoundaryPotential_old, one_mul, sub_zero,
    abs_of_nonneg (componentBoundaryDistance_nonneg _ _ _ _)] using bound

theorem open_distinct_cells_boundary_separation
    (configuration : Fin outerEdges → Configuration innerEdges)
    (first second : Fin outerEdges) (distinct : first ≠ second)
    (left right : Fin innerVertices)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner first left) (outer.cellVertex inner second right)) :
    componentBoundaryDistance (inner.openGraph (configuration first)) inner.source inner.target left +
      componentBoundaryDistance (inner.openGraph (configuration second)) inner.source inner.target right ≤
      ((outer.substitutedGraph inner configuration).dist
        (outer.cellVertex inner first left) (outer.cellVertex inner second right) : ℝ) := by
  classical
  let weight (edge : Fin outerEdges) : ℝ :=
    if edge = first then 1 else if edge = second then -1 else 0
  have bounded (edge) : |weight edge| ≤ 1 := by
    dsimp only [weight]
    split_ifs <;> norm_num
  have bound := openCellBoundaryPotential_distance outer inner configuration weight bounded reachable
  have firstWeight : weight first = 1 := by simp [weight]
  have secondWeight : weight second = -1 := by simp [weight, distinct.symm]
  simpa only [openCellBoundaryPotential_cell, firstWeight, secondWeight,
    one_mul, neg_one_mul, sub_neg_eq_add,
    abs_of_nonneg (add_nonneg (componentBoundaryDistance_nonneg _ _ _ _)
      (componentBoundaryDistance_nonneg _ _ _ _))] using bound

theorem distinct_cells_intersect_only_at_planted_vertices
    (first second : Fin outerEdges) (distinct : first ≠ second)
    (left right : Fin innerVertices)
    (equal : outer.cellVertex inner first left = outer.cellVertex inner second right) :
    (left = inner.source ∨ left = inner.target) ∧
      (right = inner.source ∨ right = inner.target) := by
  classical
  have planted (first second : Fin outerEdges) (distinct : first ≠ second)
      (left right : Fin innerVertices)
      (equal : outer.cellVertex inner first left = outer.cellVertex inner second right) :
      left = inner.source ∨ left = inner.target := by
    by_cases source : left = inner.source
    · exact Or.inl source
    by_cases target : left = inner.target
    · exact Or.inr target
    simp only [cellVertex, dif_neg source, dif_neg target] at equal
    by_cases rightSource : right = inner.source
    · simp [rightSource] at equal
    by_cases rightTarget : right = inner.target
    · simp [rightTarget, Ne.symm inner.terminals_distinct] at equal
    simp only [dif_neg rightSource, dif_neg rightTarget] at equal
    exact False.elim (distinct (congrArg Prod.fst (Sum.inr.inj equal)))
  exact ⟨planted first second distinct left right equal,
    planted second first distinct.symm right left equal.symm⟩

end IGSIII.Geometry
