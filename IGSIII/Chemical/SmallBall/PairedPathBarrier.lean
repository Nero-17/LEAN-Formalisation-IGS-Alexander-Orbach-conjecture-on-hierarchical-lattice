import IGSIII.Chemical.SmallBall.PathCountMoments
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open scoped BigOperators

noncomputable section

variable {Edge Outcome : Type*} [Fintype Edge] [DecidableEq Edge] [Fintype Outcome]

/-- Both costs are functions on the same outcome; no independence within a pair is used. -/
theorem finite_paired_exponential_le (weight first second : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (parameter scale : ℝ) :
    (∑ outcome, weight outcome * Real.exp (parameter * (first outcome - scale * second outcome))) ≤
      Real.sqrt (∑ outcome, weight outcome * Real.exp (2 * parameter * first outcome)) *
        Real.sqrt (∑ outcome, weight outcome * Real.exp (-2 * parameter * scale * second outcome)) := by
  have factor (outcome : Outcome) :
      (Real.sqrt (weight outcome) * Real.exp (parameter * first outcome)) *
          (Real.sqrt (weight outcome) * Real.exp (-parameter * scale * second outcome)) =
        weight outcome * Real.exp (parameter * (first outcome - scale * second outcome)) := by
    calc
      _ = (Real.sqrt (weight outcome) * Real.sqrt (weight outcome)) *
          (Real.exp (parameter * first outcome) * Real.exp (-parameter * scale * second outcome)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (weightNonnegative outcome), ← Real.exp_add]; congr 2 <;> ring
  have firstSquare (outcome : Outcome) :
      (Real.sqrt (weight outcome) * Real.exp (parameter * first outcome)) ^ 2 =
        weight outcome * Real.exp (2 * parameter * first outcome) := by
    rw [mul_pow, Real.sq_sqrt (weightNonnegative outcome), ← Real.exp_nat_mul]
    congr 2 <;> ring
  have secondSquare (outcome : Outcome) :
      (Real.sqrt (weight outcome) * Real.exp (-parameter * scale * second outcome)) ^ 2 =
        weight outcome * Real.exp (-2 * parameter * scale * second outcome) := by
    rw [mul_pow, Real.sq_sqrt (weightNonnegative outcome), ← Real.exp_nat_mul]
    congr 2 <;> ring
  simpa only [factor, firstSquare, secondSquare] using
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Outcome)
      (fun outcome => Real.sqrt (weight outcome) * Real.exp (parameter * first outcome))
      (fun outcome => Real.sqrt (weight outcome) * Real.exp (-parameter * scale * second outcome))

theorem finite_paired_exponential_le_of_marginals (weight first second : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (parameter scale upper lower : ℝ)
    (firstBound : (∑ outcome, weight outcome * Real.exp (2 * parameter * first outcome)) ≤ upper)
    (secondBound : (∑ outcome, weight outcome * Real.exp (-2 * parameter * scale * second outcome)) ≤ lower) :
    (∑ outcome, weight outcome * Real.exp (parameter * (first outcome - scale * second outcome))) ≤
      Real.sqrt upper * Real.sqrt lower :=
  (finite_paired_exponential_le weight first second weightNonnegative parameter scale).trans
    (mul_le_mul (Real.sqrt_le_sqrt firstBound) (Real.sqrt_le_sqrt secondBound)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem finite_product_paired_path_barrier (weight first second : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (path : Finset Edge) {parameter scale ratio : ℝ} (parameterNonnegative : 0 ≤ parameter)
    (pairedLaplace : ∀ edge ∈ path,
      (∑ outcome, weight edge outcome * Real.exp (parameter * (first edge outcome - scale * second edge outcome))) ≤ ratio) :
    (∑ outcome : Edge → Outcome,
      if scale * PathFamily.pathCost path (fun edge => second edge (outcome edge)) <
          PathFamily.pathCost path (fun edge => first edge (outcome edge))
      then ∏ edge, weight edge (outcome edge) else 0) ≤ ratio ^ path.card := by
  have costIdentity (outcome : Edge → Outcome) :
      PathFamily.pathCost path (fun edge => scale * second edge (outcome edge) - first edge (outcome edge)) =
        scale * PathFamily.pathCost path (fun edge => second edge (outcome edge)) -
          PathFamily.pathCost path (fun edge => first edge (outcome edge)) := by
    simp only [PathFamily.pathCost, Finset.sum_sub_distrib, Finset.mul_sum]
  have exponentIdentity (edge : Edge) (outcome : Outcome) :
      -parameter * (scale * second edge outcome - first edge outcome) =
        parameter * (first edge outcome - scale * second edge outcome) := by ring
  simpa only [costIdentity, exponentIdentity, mul_zero, zero_mul, Real.exp_zero, one_mul, Nat.cast_zero,
      sub_neg, sub_lt_zero] using
    finite_product_path_small_cost_bound weight (fun edge outcome => scale * second edge outcome - first edge outcome)
      weightNonnegative normalized path parameterNonnegative
      (fun edge membership => by simpa only [exponentIdentity] using pairedLaplace edge membership)
      (speed := 0)

theorem finite_product_shortest_paired_barrier (family : PathFamily Edge)
    (weight first second : Edge → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    {parameter scale ratio : ℝ} (parameterNonnegative : 0 ≤ parameter)
    (pairedLaplace : ∀ path ∈ family.paths, ∀ edge ∈ path,
      (∑ outcome, weight edge outcome * Real.exp (parameter * (first edge outcome - scale * second edge outcome))) ≤ ratio) :
    (∑ outcome : Edge → Outcome,
      if scale * family.shortest (fun edge => second edge (outcome edge)) <
          family.shortest (fun edge => first edge (outcome edge))
      then ∏ edge, weight edge (outcome edge) else 0) ≤
        ∑ path ∈ family.paths, ratio ^ path.card := by
  classical
  have eventNonnegative (path : Finset Edge) (outcome : Edge → Outcome) : 0 ≤
      (if scale * PathFamily.pathCost path (fun edge => second edge (outcome edge)) <
          PathFamily.pathCost path (fun edge => first edge (outcome edge))
      then ∏ edge, weight edge (outcome edge) else 0) := by
    split <;> first | exact Finset.prod_nonneg (fun edge _ => weightNonnegative edge (outcome edge)) | positivity
  have unionBound (outcome : Edge → Outcome) :
      (if scale * family.shortest (fun edge => second edge (outcome edge)) <
          family.shortest (fun edge => first edge (outcome edge))
      then ∏ edge, weight edge (outcome edge) else 0) ≤
        ∑ path ∈ family.paths,
          if scale * PathFamily.pathCost path (fun edge => second edge (outcome edge)) <
              PathFamily.pathCost path (fun edge => first edge (outcome edge))
          then ∏ edge, weight edge (outcome edge) else 0 := by
    split_ifs with bad
    · obtain ⟨path, membership, minimizing⟩ := family.exists_minimizer (fun edge => second edge (outcome edge))
      have pathBad : scale * PathFamily.pathCost path (fun edge => second edge (outcome edge)) <
          PathFamily.pathCost path (fun edge => first edge (outcome edge)) := by
        rw [← minimizing]
        exact bad.trans_le (family.shortest_le_pathCost _ membership)
      simpa only [if_pos pathBad] using Finset.single_le_sum
        (fun other _ => eventNonnegative other outcome) membership
    · exact Finset.sum_nonneg (fun path _ => eventNonnegative path outcome)
  calc
    _ ≤ ∑ outcome : Edge → Outcome, ∑ path ∈ family.paths,
        if scale * PathFamily.pathCost path (fun edge => second edge (outcome edge)) <
            PathFamily.pathCost path (fun edge => first edge (outcome edge))
        then ∏ edge, weight edge (outcome edge) else 0 := Finset.sum_le_sum (fun outcome _ => unionBound outcome)
    _ = ∑ path ∈ family.paths, ∑ outcome : Edge → Outcome,
        if scale * PathFamily.pathCost path (fun edge => second edge (outcome edge)) <
            PathFamily.pathCost path (fun edge => first edge (outcome edge))
        then ∏ edge, weight edge (outcome edge) else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun path membership => finite_product_paired_path_barrier weight first second
      weightNonnegative normalized path parameterNonnegative (pairedLaplace path membership))

theorem path_sum_le_geometric_tail_from_minimum (family : PathFamily Edge) (minimum : ℕ)
    (minimumLength : ∀ path ∈ family.paths, minimum ≤ path.card)
    {pathCountBase ratio : ℝ} (ratioNonnegative : 0 ≤ ratio) (pathCountBaseNonnegative : 0 ≤ pathCountBase)
    (pathCount : ∀ size : ℕ, (((family.paths.filter (fun path => path.card = size)).card : ℕ) : ℝ) ≤
      pathCountBase ^ size) (geometricBelowOne : pathCountBase * ratio < 1) :
    (∑ path ∈ family.paths, ratio ^ path.card) ≤
      (pathCountBase * ratio) ^ minimum / (1 - pathCountBase * ratio) := by
  classical
  have fiberSum := Finset.sum_fiberwise_of_maps_to
    (s := family.paths) (t := Finset.range (Fintype.card Edge + 1)) (g := fun path : Finset Edge => path.card - minimum)
    (fun path _ => Finset.mem_range.mpr (by have := Finset.card_le_univ path; omega)) (fun path => ratio ^ path.card)
  have fiberIdentity (size : ℕ) :
      (∑ path ∈ family.paths.filter (fun path => path.card - minimum = size), ratio ^ path.card) =
        ((family.paths.filter (fun path => path.card = size + minimum)).card : ℝ) * ratio ^ (size + minimum) := by
    have filterIdentity : family.paths.filter (fun path => path.card - minimum = size) =
        family.paths.filter (fun path => path.card = size + minimum) := by
      ext path
      simp only [Finset.mem_filter]
      constructor <;> rintro ⟨membership, cardinality⟩ <;>
        exact ⟨membership, by have := minimumLength path membership; omega⟩
    rw [filterIdentity]
    calc
      _ = ∑ _path ∈ family.paths.filter (fun path => path.card = size + minimum), ratio ^ (size + minimum) :=
        Finset.sum_congr rfl (fun path membership => by rw [(Finset.mem_filter.mp membership).2])
      _ = _ := by simp
  have geometricNonnegative := mul_nonneg pathCountBaseNonnegative ratioNonnegative
  have geometricSummable : Summable (fun size : ℕ => (pathCountBase * ratio) ^ (size + minimum)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one geometricNonnegative geometricBelowOne).mul_right
      ((pathCountBase * ratio) ^ minimum)
  calc
    _ = ∑ size ∈ Finset.range (Fintype.card Edge + 1),
        ((family.paths.filter (fun path => path.card = size + minimum)).card : ℝ) * ratio ^ (size + minimum) := by
      rw [← fiberSum]
      simp_rw [fiberIdentity]
    _ ≤ ∑ size ∈ Finset.range (Fintype.card Edge + 1), (pathCountBase * ratio) ^ (size + minimum) :=
      Finset.sum_le_sum (fun size _ => by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pathCount (size + minimum)) (pow_nonneg ratioNonnegative _))
    _ ≤ ∑' size : ℕ, (pathCountBase * ratio) ^ (size + minimum) :=
      geometricSummable.sum_le_tsum _ (fun size _ => pow_nonneg geometricNonnegative _)
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_of_lt_one geometricNonnegative geometricBelowOne, div_eq_mul_inv]
      ring

end
end IGSIII.Chemical.SmallBall
