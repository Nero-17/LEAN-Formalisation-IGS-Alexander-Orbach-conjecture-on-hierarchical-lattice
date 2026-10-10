import IGSIII.Chemical.PathBounds
import Universality.Probability.FiniteProductMoments
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Exponential Markov and union bounds for actual finite product weights.
The product law is expanded explicitly, rather than assumed through a
certificate of independent path costs.  Counting paths in iterated graphs is
a separate combinatorial obligation. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open scoped BigOperators

noncomputable section

variable {Edge Outcome : Type*} [Fintype Edge] [DecidableEq Edge] [Fintype Outcome]

theorem finite_product_path_exponential (weight response : Edge → Outcome → ℝ)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1) (path : Finset Edge) :
    (∑ outcome : Edge → Outcome, (∏ edge, weight edge (outcome edge)) *
      Real.exp (∑ edge ∈ path, response edge (outcome edge))) =
      ∏ edge ∈ path, ∑ outcome, weight edge outcome * Real.exp (response edge outcome) := by
  classical
  have factor (outcome : Edge → Outcome) :
      (∏ edge, weight edge (outcome edge)) *
        Real.exp (∑ edge ∈ path, response edge (outcome edge)) =
      ∏ edge, weight edge (outcome edge) *
        (if edge ∈ path then Real.exp (response edge (outcome edge)) else 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Real.exp_sum]
  simp_rw [factor]
  rw [← Fintype.prod_sum (fun edge outcome => weight edge outcome *
    (if edge ∈ path then Real.exp (response edge outcome) else 1))]
  have localFactor (edge : Edge) :
      (∑ outcome, weight edge outcome *
        (if edge ∈ path then Real.exp (response edge outcome) else 1)) =
        if edge ∈ path then ∑ outcome, weight edge outcome * Real.exp (response edge outcome)
          else 1 := by
    by_cases within : edge ∈ path <;> simp [within, normalized]
  simp_rw [localFactor]
  exact Finset.prod_ite_mem_eq path _

theorem finite_exponential_markov (weight response : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    {parameter : ℝ} (parameterNonnegative : 0 ≤ parameter) (threshold : ℝ) :
    (∑ outcome, if response outcome < threshold then weight outcome else 0) ≤
      Real.exp (parameter * threshold) *
        ∑ outcome, weight outcome * Real.exp (-parameter * response outcome) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro outcome _
  by_cases below : response outcome < threshold
  · rw [if_pos below]
    have exponentialBound : 1 ≤ Real.exp (parameter * threshold) *
        Real.exp (-parameter * response outcome) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    have multiplied := mul_le_mul_of_nonneg_left exponentialBound (nonnegative outcome)
    nlinarith
  · rw [if_neg below]
    exact mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (nonnegative outcome) (Real.exp_nonneg _))

theorem finite_product_path_small_cost_bound (weight cost : Edge → Outcome → ℝ)
    (nonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (path : Finset Edge) {parameter laplace speed : ℝ}
    (parameterNonnegative : 0 ≤ parameter)
    (laplaceBound : ∀ edge ∈ path,
      (∑ outcome, weight edge outcome * Real.exp (-parameter * cost edge outcome)) ≤ laplace) :
    (∑ outcome : Edge → Outcome,
      if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
      then ∏ edge, weight edge (outcome edge) else 0) ≤
        (Real.exp (parameter * speed) * laplace) ^ path.card := by
  have markov := finite_exponential_markov (fun outcome : Edge → Outcome =>
      ∏ edge, weight edge (outcome edge))
    (fun outcome => PathFamily.pathCost path (fun edge => cost edge (outcome edge)))
    (fun outcome => Finset.prod_nonneg (fun edge _ => nonnegative edge (outcome edge)))
    parameterNonnegative (speed * path.card)
  have exponent (outcome : Edge → Outcome) :
      -parameter * PathFamily.pathCost path (fun edge => cost edge (outcome edge)) =
        ∑ edge ∈ path, -parameter * cost edge (outcome edge) := by
    simp only [PathFamily.pathCost, Finset.mul_sum]
  simp_rw [exponent] at markov
  rw [finite_product_path_exponential weight (fun edge outcome => -parameter * cost edge outcome)
    normalized path] at markov
  have productBound : (∏ edge ∈ path,
      ∑ outcome, weight edge outcome * Real.exp (-parameter * cost edge outcome)) ≤
      laplace ^ path.card := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod
      (fun edge _ => Finset.sum_nonneg (fun outcome _ =>
        mul_nonneg (nonnegative edge outcome) (Real.exp_nonneg _))) laplaceBound
  have exponentialIdentity : Real.exp (parameter * (speed * path.card)) =
      Real.exp (parameter * speed) ^ path.card := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ Real.exp (parameter * (speed * path.card)) * laplace ^ path.card :=
      markov.trans (mul_le_mul_of_nonneg_left productBound (Real.exp_nonneg _))
    _ = _ := by rw [exponentialIdentity, mul_pow]

theorem finite_product_shortest_small_cost_bound (family : PathFamily Edge)
    (weight cost : Edge → Outcome → ℝ)
    (nonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    {parameter laplace speed : ℝ} (parameterNonnegative : 0 ≤ parameter)
    (speedNonnegative : 0 ≤ speed)
    (laplaceBound : ∀ edge,
      (∑ outcome, weight edge outcome * Real.exp (-parameter * cost edge outcome)) ≤ laplace) :
    (∑ outcome : Edge → Outcome,
      if family.shortest (fun edge => cost edge (outcome edge)) <
        speed * family.shortest (fun _ => 1)
      then ∏ edge, weight edge (outcome edge) else 0) ≤
        ∑ path ∈ family.paths, (Real.exp (parameter * speed) * laplace) ^ path.card := by
  classical
  have unionBound (outcome : Edge → Outcome) :
      (if family.shortest (fun edge => cost edge (outcome edge)) <
        speed * family.shortest (fun _ => 1)
      then ∏ edge, weight edge (outcome edge) else 0) ≤
      ∑ path ∈ family.paths,
        if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
        then ∏ edge, weight edge (outcome edge) else 0 := by
    have eventNonnegative (path : Finset Edge) : 0 ≤
        (if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
        then ∏ edge, weight edge (outcome edge) else 0) := by
      by_cases below : PathFamily.pathCost path (fun edge => cost edge (outcome edge)) <
          speed * path.card
      · rw [if_pos below]
        exact Finset.prod_nonneg (fun edge _ => nonnegative edge (outcome edge))
      · rw [if_neg below]
    split_ifs with below
    · obtain ⟨path, membership, minimizing⟩ := family.exists_minimizer
        (fun edge => cost edge (outcome edge))
      have cardinalBound : family.shortest (fun _ => 1) ≤ (path.card : ℝ) := by
        simpa only [PathFamily.pathCost, Finset.sum_const, nsmul_eq_mul, mul_one] using
          family.shortest_le_pathCost (fun _ => 1) membership
      have pathBelow : PathFamily.pathCost path (fun edge => cost edge (outcome edge)) <
          speed * path.card := by
        rw [← minimizing]
        exact below.trans_le (mul_le_mul_of_nonneg_left cardinalBound speedNonnegative)
      have single := Finset.single_le_sum (fun other _ => eventNonnegative other) membership
      simpa only [if_pos pathBelow] using single
    · exact Finset.sum_nonneg (fun path _ => eventNonnegative path)
  calc
    _ ≤ ∑ outcome : Edge → Outcome, ∑ path ∈ family.paths,
        if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
        then ∏ edge, weight edge (outcome edge) else 0 :=
      Finset.sum_le_sum (fun outcome _ => unionBound outcome)
    _ = ∑ path ∈ family.paths, ∑ outcome : Edge → Outcome,
        if PathFamily.pathCost path (fun edge => cost edge (outcome edge)) < speed * path.card
        then ∏ edge, weight edge (outcome edge) else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun path _ => finite_product_path_small_cost_bound weight cost
      nonnegative normalized path parameterNonnegative
      (fun edge _ => laplaceBound edge))

end
end IGSIII.Chemical.SmallBall
