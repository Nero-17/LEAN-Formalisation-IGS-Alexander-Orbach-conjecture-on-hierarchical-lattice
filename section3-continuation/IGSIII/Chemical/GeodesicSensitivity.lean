import IGSIII.Chemical.PathFunctional
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs

/-!
# A geodesic controls coordinate resampling

Changing one edge cost changes a shortest-path value only through a selected
old or new geodesic. The choice is made from the actual finite path family.
-/

set_option autoImplicit false

namespace IGSIII.Chemical.PathFamily

open Finset

variable {Edge : Type*} [DecidableEq Edge]

noncomputable def minimizingPath (family : PathFamily Edge) (cost : Edge → ℝ) : Finset Edge :=
  (family.exists_minimizer cost).choose

theorem minimizingPath_mem (family : PathFamily Edge) (cost : Edge → ℝ) :
    family.minimizingPath cost ∈ family.paths :=
  (family.exists_minimizer cost).choose_spec.1

theorem minimizingPath_cost (family : PathFamily Edge) (cost : Edge → ℝ) :
    pathCost (family.minimizingPath cost) cost = family.shortest cost :=
  (family.exists_minimizer cost).choose_spec.2.symm

theorem pathCost_update (path : Finset Edge) (cost : Edge → ℝ)
    (changed : Edge) (replacement : ℝ) :
    pathCost path (Function.update cost changed replacement) =
      pathCost path cost + if changed ∈ path then replacement - cost changed else 0 := by
  by_cases membership : changed ∈ path
  · have identity (edge : Edge) :
        Function.update cost changed replacement edge = cost edge +
          if edge = changed then replacement - cost changed else 0 := by
      by_cases equal : edge = changed <;> simp [equal]
    simp only [pathCost, identity, Finset.sum_add_distrib]
    simp [membership]
  · have equal (edge : Edge) (present : edge ∈ path) :
        Function.update cost changed replacement edge = cost edge := by
      have distinct : edge ≠ changed := fun equality => membership (equality ▸ present)
      exact Function.update_of_ne distinct replacement cost
    simp only [if_neg membership, add_zero]
    exact Finset.sum_congr rfl equal

theorem shortest_update_sub_le_geodesic (family : PathFamily Edge) (cost : Edge → ℝ)
    (changed : Edge) (replacement : ℝ) :
    family.shortest (Function.update cost changed replacement) - family.shortest cost ≤
      if changed ∈ family.minimizingPath cost then replacement - cost changed else 0 := by
  have bound := family.shortest_le_pathCost (Function.update cost changed replacement)
    (family.minimizingPath_mem cost)
  rw [pathCost_update, minimizingPath_cost] at bound
  linarith

theorem shortest_update_eq_of_both_geodesics_avoid (family : PathFamily Edge) (cost : Edge → ℝ)
    (changed : Edge) (replacement : ℝ)
    (oldAvoids : changed ∉ family.minimizingPath cost)
    (newAvoids : changed ∉ family.minimizingPath (Function.update cost changed replacement)) :
    family.shortest (Function.update cost changed replacement) = family.shortest cost := by
  have forward := family.shortest_update_sub_le_geodesic cost changed replacement
  simp only [if_neg oldAvoids] at forward
  have backward := family.shortest_update_sub_le_geodesic
    (Function.update cost changed replacement) changed (cost changed)
  have restored : Function.update (Function.update cost changed replacement) changed (cost changed) = cost := by
    funext edge
    by_cases equal : edge = changed <;> simp [equal]
  simp only [restored, if_neg newAvoids] at backward
  linarith

variable [Fintype Edge]

theorem shortest_update_abs_le (family : PathFamily Edge) (cost : Edge → ℝ)
    (changed : Edge) (replacement : ℝ) :
    |family.shortest (Function.update cost changed replacement) - family.shortest cost| ≤
      |replacement - cost changed| := by
  have bound := family.shortest_lipschitz (Function.update cost changed replacement) cost
  have sum : (∑ edge, |Function.update cost changed replacement edge - cost edge|) =
      |replacement - cost changed| := by
    rw [Finset.sum_eq_single changed]
    · simp
    · intro edge _ distinct
      simp [Function.update_of_ne distinct]
    · simp
  exact bound.trans_eq sum

theorem shortest_update_sq_le_geodesic_indicators (family : PathFamily Edge) (cost : Edge → ℝ)
    (changed : Edge) (replacement : ℝ) :
    (family.shortest (Function.update cost changed replacement) - family.shortest cost) ^ 2 ≤
      (replacement - cost changed) ^ 2 *
        ((if changed ∈ family.minimizingPath cost then (1 : ℝ) else 0) +
          if changed ∈ family.minimizingPath (Function.update cost changed replacement) then 1 else 0) := by
  have absolute := family.shortest_update_abs_le cost changed replacement
  have squared : (family.shortest (Function.update cost changed replacement) - family.shortest cost) ^ 2 ≤
      (replacement - cost changed) ^ 2 := by
    exact sq_le_sq.mpr absolute
  by_cases oldMember : changed ∈ family.minimizingPath cost <;>
    by_cases newMember : changed ∈ family.minimizingPath (Function.update cost changed replacement)
  · simp only [if_pos oldMember, if_pos newMember]
    nlinarith [sq_nonneg (replacement - cost changed)]
  · simpa only [if_pos oldMember, if_neg newMember, add_zero, mul_one] using squared
  · simpa only [if_neg oldMember, if_pos newMember, zero_add, mul_one] using squared
  · simp [oldMember, newMember,
      family.shortest_update_eq_of_both_geodesics_avoid cost changed replacement oldMember newMember]

end IGSIII.Chemical.PathFamily
