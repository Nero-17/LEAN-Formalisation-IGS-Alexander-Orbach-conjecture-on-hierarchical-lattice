import IGSIII.Chemical.SmallBall.PathLaplace
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open scoped BigOperators

noncomputable section

variable {Edge Outcome : Type*} [Fintype Edge] [DecidableEq Edge] [Fintype Outcome]

theorem finite_product_shortest_small_cost_bound_on_paths (family : PathFamily Edge)
    (weight cost : Edge → Outcome → ℝ)
    (nonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    {parameter laplace speed : ℝ} (parameterNonnegative : 0 ≤ parameter)
    (speedNonnegative : 0 ≤ speed)
    (laplaceBound : ∀ path ∈ family.paths, ∀ edge ∈ path,
      (∑ outcome, weight edge outcome * Real.exp (-parameter * cost edge outcome)) ≤ laplace) :
    (∑ outcome : Edge → Outcome,
      if family.shortest (fun edge => cost edge (outcome edge)) <
        speed * family.shortest (fun _ => 1)
      then ∏ edge, weight edge (outcome edge) else 0) ≤
        ∑ path ∈ family.paths, (Real.exp (parameter * speed) * laplace) ^ path.card := by
  classical
  have eventNonnegative (path : Finset Edge) (outcome : Edge → Outcome) : 0 ≤
      (if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
      then ∏ edge, weight edge (outcome edge) else 0) := by
    split <;> first | exact Finset.prod_nonneg (fun edge _ => nonnegative edge (outcome edge)) | positivity
  have unionBound (outcome : Edge → Outcome) :
      (if family.shortest (fun edge => cost edge (outcome edge)) < speed * family.shortest (fun _ => 1)
      then ∏ edge, weight edge (outcome edge) else 0) ≤
        ∑ path ∈ family.paths,
          if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
          then ∏ edge, weight edge (outcome edge) else 0 := by
    split_ifs with below
    · obtain ⟨path, membership, minimizing⟩ := family.exists_minimizer (fun edge => cost edge (outcome edge))
      have cardinalBound : family.shortest (fun _ => 1) ≤ (path.card : ℝ) := by
        simpa only [PathFamily.pathCost, Finset.sum_const, nsmul_eq_mul, mul_one] using
          family.shortest_le_pathCost (fun _ => 1) membership
      have pathBelow : PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card := by
        rw [← minimizing]
        exact below.trans_le (mul_le_mul_of_nonneg_left cardinalBound speedNonnegative)
      simpa only [if_pos pathBelow] using Finset.single_le_sum
        (fun other _ => eventNonnegative other outcome) membership
    · exact Finset.sum_nonneg (fun path _ => eventNonnegative path outcome)
  calc
    _ ≤ ∑ outcome : Edge → Outcome, ∑ path ∈ family.paths,
        if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
        then ∏ edge, weight edge (outcome edge) else 0 := Finset.sum_le_sum (fun outcome _ => unionBound outcome)
    _ = ∑ path ∈ family.paths, ∑ outcome : Edge → Outcome,
        if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
        then ∏ edge, weight edge (outcome edge) else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun path membership => finite_product_path_small_cost_bound weight cost
      nonnegative normalized path parameterNonnegative (laplaceBound path membership))

theorem path_sum_le_geometric_tail (family : PathFamily Edge)
    (nonemptyPaths : ∀ path ∈ family.paths, 0 < path.card)
    {pathCountBase ratio : ℝ} (ratioNonnegative : 0 ≤ ratio) (pathCountBaseNonnegative : 0 ≤ pathCountBase)
    (pathCount : ∀ size : ℕ, (((family.paths.filter (fun path => path.card = size)).card : ℕ) : ℝ) ≤
      pathCountBase ^ size)
    (geometricBelowOne : pathCountBase * ratio < 1) :
    (∑ path ∈ family.paths, ratio ^ path.card) ≤
      (pathCountBase * ratio) / (1 - pathCountBase * ratio) := by
  classical
  have fiberSum := Finset.sum_fiberwise_of_maps_to
    (s := family.paths) (t := Finset.range (Fintype.card Edge)) (g := fun path : Finset Edge => path.card - 1)
    (fun path membership => Finset.mem_range.mpr (by
      have lower := nonemptyPaths path membership
      have upper := Finset.card_le_univ path
      omega)) (fun path => ratio ^ path.card)
  have fiberIdentity (size : ℕ) :
      (∑ path ∈ family.paths.filter (fun path => path.card - 1 = size), ratio ^ path.card) =
        ((family.paths.filter (fun path => path.card = size + 1)).card : ℝ) * ratio ^ (size + 1) := by
    have filterIdentity : family.paths.filter (fun path => path.card - 1 = size) =
        family.paths.filter (fun path => path.card = size + 1) := by
      ext path
      simp only [Finset.mem_filter]
      constructor <;> rintro ⟨membership, cardinality⟩ <;>
        exact ⟨membership, by have := nonemptyPaths path membership; omega⟩
    rw [filterIdentity]
    calc
      _ = ∑ _path ∈ family.paths.filter (fun path => path.card = size + 1), ratio ^ (size + 1) :=
        Finset.sum_congr rfl (fun path membership => by rw [(Finset.mem_filter.mp membership).2])
      _ = _ := by simp
  have geometricNonnegative := mul_nonneg pathCountBaseNonnegative ratioNonnegative
  have geometricSummable : Summable (fun size : ℕ => (pathCountBase * ratio) ^ (size + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one geometricNonnegative geometricBelowOne).mul_right
      (pathCountBase * ratio)
  calc
    _ = ∑ size ∈ Finset.range (Fintype.card Edge),
        ((family.paths.filter (fun path => path.card = size + 1)).card : ℝ) * ratio ^ (size + 1) := by
      rw [← fiberSum]
      simp_rw [fiberIdentity]
    _ ≤ ∑ size ∈ Finset.range (Fintype.card Edge), (pathCountBase * ratio) ^ (size + 1) :=
      Finset.sum_le_sum (fun size _ => by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pathCount (size + 1)) (pow_nonneg ratioNonnegative _))
    _ ≤ ∑' size : ℕ, (pathCountBase * ratio) ^ (size + 1) :=
      geometricSummable.sum_le_tsum _ (fun size _ => pow_nonneg geometricNonnegative _)
    _ = _ := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one geometricNonnegative geometricBelowOne, div_eq_mul_inv]
      ring

theorem finite_mean_lower_of_small_tail (weight value : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (valueNonnegative : ∀ outcome, 0 ≤ value outcome) {threshold : ℝ} (thresholdNonnegative : 0 ≤ threshold)
    (smallTail : (∑ outcome, if value outcome < threshold then weight outcome else 0) ≤ (1 / 2 : ℝ)) :
    threshold / 2 ≤ ∑ outcome, weight outcome * value outcome := by
  have pointwise (outcome : Outcome) :
      threshold * (weight outcome - (if value outcome < threshold then weight outcome else 0)) ≤
        weight outcome * value outcome := by
    by_cases small : value outcome < threshold
    · simp only [small, if_true, sub_self, mul_zero]
      exact mul_nonneg (weightNonnegative outcome) (valueNonnegative outcome)
    · simp only [small, if_false, sub_zero]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (le_of_not_gt small) (weightNonnegative outcome)
  have comparison := Finset.sum_le_sum (fun outcome (_ : outcome ∈ Finset.univ) => pointwise outcome)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, normalized] at comparison
  nlinarith

theorem finite_product_shortest_mean_lower (family : PathFamily Edge)
    (nonemptyPaths : ∀ path ∈ family.paths, 0 < path.card)
    (weight cost : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (costNonnegative : ∀ edge outcome, 0 ≤ cost edge outcome)
    {parameter laplace speed pathCountBase : ℝ} (parameterNonnegative : 0 ≤ parameter)
    (laplaceNonnegative : 0 ≤ laplace) (speedNonnegative : 0 ≤ speed)
    (pathCountBaseNonnegative : 0 ≤ pathCountBase)
    (laplaceBound : ∀ path ∈ family.paths, ∀ edge ∈ path,
      (∑ outcome, weight edge outcome * Real.exp (-parameter * cost edge outcome)) ≤ laplace)
    (pathCount : ∀ size : ℕ, (((family.paths.filter (fun path => path.card = size)).card : ℕ) : ℝ) ≤
      pathCountBase ^ size)
    (geometricBelowOne : pathCountBase * (Real.exp (parameter * speed) * laplace) < 1)
    (geometricBound : (pathCountBase * (Real.exp (parameter * speed) * laplace)) /
      (1 - pathCountBase * (Real.exp (parameter * speed) * laplace)) ≤ (1 / 2 : ℝ)) :
    (speed / 2) * family.shortest (fun _ => 1) ≤
      ∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
        family.shortest (fun edge => cost edge (outcome edge)) := by
  have smallTail := (finite_product_shortest_small_cost_bound_on_paths family weight cost
    weightNonnegative normalized parameterNonnegative speedNonnegative laplaceBound).trans
      ((path_sum_le_geometric_tail family nonemptyPaths
        (mul_nonneg (Real.exp_nonneg _) laplaceNonnegative) pathCountBaseNonnegative
        pathCount geometricBelowOne).trans geometricBound)
  have normalizedProduct : (∑ outcome : Edge → Outcome, ∏ edge, weight edge (outcome edge)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [normalized, Finset.prod_const_one]
  have lower := finite_mean_lower_of_small_tail (fun outcome : Edge → Outcome => ∏ edge, weight edge (outcome edge))
    (fun outcome => family.shortest (fun edge => cost edge (outcome edge)))
    (fun outcome => Finset.prod_nonneg (fun edge _ => weightNonnegative edge (outcome edge))) normalizedProduct
    (fun outcome => family.shortest_nonneg (fun edge => costNonnegative edge (outcome edge)))
    (mul_nonneg speedNonnegative (family.shortest_nonneg (fun _ => zero_le_one))) smallTail
  convert lower using 1 <;> ring

end
end IGSIII.Chemical.SmallBall
