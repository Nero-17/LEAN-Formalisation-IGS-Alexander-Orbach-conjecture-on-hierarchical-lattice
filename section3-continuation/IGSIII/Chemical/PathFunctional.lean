import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# Finite shortest-path functionals

Section 2, paragraph preceding Theorem `chemical-scalar`.
A path is represented by its edge set. This module establishes the analytic
properties for every nonempty finite family of such sets; it does not assert
that an arbitrary family comes from a graph.
-/

namespace IGSIII.Chemical

open Finset

variable {Edge : Type*} [DecidableEq Edge]

/-- The finite, nonempty collection of edge sets of admissible terminal paths. -/
structure PathFamily (Edge : Type*) [DecidableEq Edge] where
  paths : Finset (Finset Edge)
  nonempty : paths.Nonempty

namespace PathFamily

def pathCost (path : Finset Edge) (cost : Edge → ℝ) : ℝ :=
  ∑ edge ∈ path, cost edge

noncomputable def shortest (family : PathFamily Edge) (cost : Edge → ℝ) : ℝ := by
  classical
  exact (family.paths.image (fun path => pathCost path cost)).min'
    (family.nonempty.image _)

theorem shortest_le_pathCost (family : PathFamily Edge) (cost : Edge → ℝ)
    {path : Finset Edge} (membership : path ∈ family.paths) :
    family.shortest cost ≤ pathCost path cost := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨path, membership, rfl⟩)

theorem le_shortest (family : PathFamily Edge) (cost : Edge → ℝ) (bound : ℝ)
    (pathwise : ∀ path ∈ family.paths, bound ≤ pathCost path cost) :
    bound ≤ family.shortest cost := by
  classical
  apply Finset.le_min'
  intro value membership
  obtain ⟨path, pathMembership, rfl⟩ := Finset.mem_image.mp membership
  exact pathwise path pathMembership

theorem exists_minimizer (family : PathFamily Edge) (cost : Edge → ℝ) :
    ∃ path ∈ family.paths, family.shortest cost = pathCost path cost := by
  classical
  have membership := Finset.min'_mem
    (family.paths.image (fun path => pathCost path cost)) (family.nonempty.image _)
  obtain ⟨path, membership, equality⟩ := Finset.mem_image.mp membership
  exact ⟨path, membership, equality.symm⟩

theorem shortest_mono (family : PathFamily Edge) {first second : Edge → ℝ}
    (comparison : ∀ edge, first edge ≤ second edge) :
    family.shortest first ≤ family.shortest second := by
  apply family.le_shortest
  intro path membership
  exact (family.shortest_le_pathCost first membership).trans
    (Finset.sum_le_sum fun edge _ => comparison edge)

theorem shortest_nonneg (family : PathFamily Edge) {cost : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ cost edge) : 0 ≤ family.shortest cost := by
  apply family.le_shortest
  intro path _
  exact Finset.sum_nonneg fun edge _ => nonnegative edge

@[simp] theorem shortest_zero (family : PathFamily Edge) :
    family.shortest (fun _ => 0) = 0 := by
  apply le_antisymm
  · obtain ⟨path, membership⟩ := family.nonempty
    simpa [pathCost] using family.shortest_le_pathCost (fun _ => 0) membership
  · exact family.shortest_nonneg fun _ => le_rfl

omit [DecidableEq Edge] in
theorem pathCost_scale (path : Finset Edge) (scalar : ℝ) (cost : Edge → ℝ) :
    pathCost path (fun edge => scalar * cost edge) = scalar * pathCost path cost := by
  simp [pathCost, Finset.mul_sum]

theorem shortest_scale (family : PathFamily Edge) (cost : Edge → ℝ)
    {scalar : ℝ} (nonnegative : 0 ≤ scalar) :
    family.shortest (fun edge => scalar * cost edge) = scalar * family.shortest cost := by
  apply le_antisymm
  · obtain ⟨path, membership, equality⟩ := family.exists_minimizer cost
    calc
      family.shortest (fun edge => scalar * cost edge) ≤
          pathCost path (fun edge => scalar * cost edge) :=
        family.shortest_le_pathCost _ membership
      _ = scalar * family.shortest cost := by rw [pathCost_scale, equality]
  · apply family.le_shortest
    intro path membership
    rw [pathCost_scale]
    exact mul_le_mul_of_nonneg_left (family.shortest_le_pathCost cost membership) nonnegative

theorem shortest_superadditive (family : PathFamily Edge) (first second : Edge → ℝ) :
    family.shortest first + family.shortest second ≤
      family.shortest (fun edge => first edge + second edge) := by
  apply family.le_shortest
  intro path membership
  simpa [pathCost, Finset.sum_add_distrib] using
    add_le_add (family.shortest_le_pathCost first membership)
      (family.shortest_le_pathCost second membership)

theorem shortest_concave (family : PathFamily Edge) (first second : Edge → ℝ)
    {firstWeight secondWeight : ℝ} (firstNonnegative : 0 ≤ firstWeight)
    (secondNonnegative : 0 ≤ secondWeight) :
    firstWeight * family.shortest first + secondWeight * family.shortest second ≤
      family.shortest (fun edge => firstWeight * first edge + secondWeight * second edge) := by
  simpa [family.shortest_scale first firstNonnegative,
    family.shortest_scale second secondNonnegative] using
    family.shortest_superadditive (fun edge => firstWeight * first edge)
      (fun edge => secondWeight * second edge)

theorem shortest_concaveOn (family : PathFamily Edge) :
    ConcaveOn ℝ Set.univ family.shortest := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ firstWeight secondWeight firstNonnegative secondNonnegative _
  exact family.shortest_concave first second firstNonnegative secondNonnegative

variable [Fintype Edge]

omit [DecidableEq Edge] in
theorem pathCost_difference_le (path : Finset Edge) (first second : Edge → ℝ) :
    pathCost path first - pathCost path second ≤ ∑ edge, |first edge - second edge| := by
  calc
    pathCost path first - pathCost path second = ∑ edge ∈ path, (first edge - second edge) := by
      simp [pathCost, Finset.sum_sub_distrib]
    _ ≤ ∑ edge ∈ path, |first edge - second edge| :=
      Finset.sum_le_sum fun edge _ => le_abs_self _
    _ ≤ ∑ edge, |first edge - second edge| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ path)
        (fun edge _ _ => abs_nonneg _)

theorem shortest_sub_le (family : PathFamily Edge) (first second : Edge → ℝ) :
    family.shortest first - family.shortest second ≤ ∑ edge, |first edge - second edge| := by
  obtain ⟨path, membership, equality⟩ := family.exists_minimizer second
  calc
    family.shortest first - family.shortest second ≤ pathCost path first - pathCost path second :=
      sub_le_sub (family.shortest_le_pathCost first membership) (le_of_eq equality.symm)
    _ ≤ ∑ edge, |first edge - second edge| := pathCost_difference_le path first second

theorem shortest_lipschitz (family : PathFamily Edge) (first second : Edge → ℝ) :
    |family.shortest first - family.shortest second| ≤ ∑ edge, |first edge - second edge| := by
  apply abs_le.mpr
  constructor
  · have comparison := family.shortest_sub_le second first
    simp only [abs_sub_comm] at comparison
    linarith
  · exact family.shortest_sub_le first second

end PathFamily
end IGSIII.Chemical

