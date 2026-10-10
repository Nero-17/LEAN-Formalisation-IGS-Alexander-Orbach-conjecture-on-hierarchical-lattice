import IGSIII.Chemical.PathFunctional

/-!
# Pivotal-edge and small-cost bounds

These are deterministic ingredients of Appendix A's moment argument.
No independence, probability law, or recursive eigenlaw is assumed or proved.
-/

set_option autoImplicit false

namespace IGSIII.Chemical.PathFamily

open Finset

variable {Edge : Type*} [DecidableEq Edge] [Fintype Edge]

/-- Edges present in every admissible terminal path. -/
def commonEdges (family : PathFamily Edge) : Finset Edge :=
  Finset.univ.filter fun edge => ∀ path ∈ family.paths, edge ∈ path

theorem commonEdges_subset (family : PathFamily Edge) {path : Finset Edge}
    (membership : path ∈ family.paths) : family.commonEdges ⊆ path := by
  intro edge edgeMembership
  exact (Finset.mem_filter.mp edgeMembership).2 path membership

theorem commonEdges_cost_le_shortest (family : PathFamily Edge) {cost : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ cost edge) :
    pathCost family.commonEdges cost ≤ family.shortest cost := by
  apply family.le_shortest
  intro path membership
  exact Finset.sum_le_sum_of_subset_of_nonneg (family.commonEdges_subset membership)
    (fun edge _ _ => nonnegative edge)

theorem shortest_le_total_cost (family : PathFamily Edge) {cost : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ cost edge) :
    family.shortest cost ≤ ∑ edge, cost edge := by
  obtain ⟨path, membership⟩ := family.nonempty
  exact (family.shortest_le_pathCost cost membership).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ path)
      (fun edge _ _ => nonnegative edge))

omit [Fintype Edge] in
theorem shortest_eq_zero_iff (family : PathFamily Edge) {cost : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ cost edge) :
    family.shortest cost = 0 ↔ ∃ path ∈ family.paths, ∀ edge ∈ path, cost edge = 0 := by
  constructor
  · intro zeroCost
    obtain ⟨path, membership, minimizing⟩ := family.exists_minimizer cost
    refine ⟨path, membership, ?_⟩
    have zeroSum : ∑ edge ∈ path, cost edge = 0 := by
      change pathCost path cost = 0
      rw [← minimizing, zeroCost]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun edge _ => nonnegative edge)).mp zeroSum
  · rintro ⟨path, membership, zeroEdges⟩
    apply le_antisymm
    · calc
        family.shortest cost ≤ pathCost path cost := family.shortest_le_pathCost cost membership
        _ = 0 := Finset.sum_eq_zero zeroEdges
    · exact family.shortest_nonneg nonnegative

omit [Fintype Edge] in
theorem low_cost_path_has_low_cost_edges (family : PathFamily Edge) {cost : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ cost edge) {threshold : ℝ}
    (lowCost : family.shortest cost ≤ threshold) :
    ∃ path ∈ family.paths, ∀ edge ∈ path, cost edge ≤ threshold := by
  obtain ⟨path, membership, minimizing⟩ := family.exists_minimizer cost
  refine ⟨path, membership, ?_⟩
  intro edge edgeMembership
  calc
    cost edge ≤ ∑ other ∈ path, cost other :=
      Finset.single_le_sum (fun other _ => nonnegative other) edgeMembership
    _ = family.shortest cost := minimizing.symm
    _ ≤ threshold := lowCost

omit [Fintype Edge] in
/-- Allowing more routes can only decrease the terminal distance. -/
theorem shortest_antitone_paths (firstFamily secondFamily : PathFamily Edge)
    (inclusion : firstFamily.paths ⊆ secondFamily.paths) (cost : Edge → ℝ) :
    secondFamily.shortest cost ≤ firstFamily.shortest cost := by
  apply firstFamily.le_shortest
  intro path membership
  exact secondFamily.shortest_le_pathCost cost (inclusion membership)

end IGSIII.Chemical.PathFamily
