import Universality.Probability.FiniteProductVariance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite product variance tensorization

All averages below are finite sums with nonnegative normalized weights.
The two-block inequality is the inductive step for Efron--Stein, including
finite conditional innovation laws. No independence or variance bound is
introduced as an assumed certificate.
-/

set_option autoImplicit false

namespace IGSIII34.Probability

open Universality
open scoped BigOperators

variable {Outcome First Second : Type*} [Fintype Outcome] [Fintype First] [Fintype Second]

def finiteMean (weight response : Outcome → ℝ) : ℝ :=
  ∑ outcome, weight outcome * response outcome

def finiteVariance (weight response : Outcome → ℝ) : ℝ :=
  ∑ outcome, weight outcome * (response outcome - finiteMean weight response) ^ 2

theorem finiteMean_add (weight first second : Outcome → ℝ) :
    finiteMean weight (fun outcome => first outcome + second outcome) =
      finiteMean weight first + finiteMean weight second := by
  simp only [finiteMean, mul_add, Finset.sum_add_distrib]

theorem finiteMean_const (weight : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) (value : ℝ) :
    finiteMean weight (fun _ => value) = value := by
  simp only [finiteMean, ← Finset.sum_mul, normalized, one_mul]

theorem finiteVariance_eq_second_moment (weight response : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) :
    finiteVariance weight response = finiteMean weight (fun outcome => response outcome ^ 2) -
      (finiteMean weight response) ^ 2 :=
  finite_weighted_variance weight response normalized

theorem finiteMean_product (firstWeight : First → ℝ) (secondWeight : Second → ℝ)
    (response : First → Second → ℝ) :
    finiteMean (fun outcome : First × Second => firstWeight outcome.1 * secondWeight outcome.2)
      (fun outcome => response outcome.1 outcome.2) =
      finiteMean firstWeight (fun first => finiteMean secondWeight (response first)) := by
  simp only [finiteMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem product_weight_normalized (firstWeight : First → ℝ) (secondWeight : Second → ℝ)
    (firstNormalized : ∑ first, firstWeight first = 1)
    (secondNormalized : ∑ second, secondWeight second = 1) :
    ∑ outcome : First × Second, firstWeight outcome.1 * secondWeight outcome.2 = 1 := by
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, secondNormalized, mul_one, firstNormalized]

theorem finiteMean_swap (firstWeight : First → ℝ) (secondWeight : Second → ℝ)
    (response : First → Second → ℝ) :
    finiteMean firstWeight (fun first => finiteMean secondWeight (response first)) =
      finiteMean secondWeight (fun second => finiteMean firstWeight (fun first => response first second)) := by
  simp only [finiteMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext second
  apply Finset.sum_congr rfl
  intro first _
  ring

theorem finiteVariance_product_decomposition
    (firstWeight : First → ℝ) (secondWeight : Second → ℝ)
    (firstNormalized : ∑ first, firstWeight first = 1)
    (secondNormalized : ∑ second, secondWeight second = 1)
    (response : First → Second → ℝ) :
    finiteVariance (fun outcome : First × Second => firstWeight outcome.1 * secondWeight outcome.2)
      (fun outcome => response outcome.1 outcome.2) =
      finiteMean firstWeight (fun first => finiteVariance secondWeight (response first)) +
        finiteVariance firstWeight (fun first => finiteMean secondWeight (response first)) := by
  rw [finiteVariance_eq_second_moment _ _
    (product_weight_normalized firstWeight secondWeight firstNormalized secondNormalized)]
  rw [finiteMean_product firstWeight secondWeight (fun first second => response first second ^ 2)]
  rw [finiteMean_product firstWeight secondWeight response]
  simp_rw [finiteVariance_eq_second_moment _ _ secondNormalized]
  rw [finiteVariance_eq_second_moment _ _ firstNormalized]
  simp only [finiteMean, mul_sub, Finset.sum_sub_distrib]
  ring

theorem variance_of_finite_average_le
    (firstWeight : First → ℝ) (secondWeight : Second → ℝ)
    (firstNonnegative : ∀ first, 0 ≤ firstWeight first)
    (secondNonnegative : ∀ second, 0 ≤ secondWeight second)
    (secondNormalized : ∑ second, secondWeight second = 1)
    (response : First → Second → ℝ) :
    finiteVariance firstWeight (fun first => finiteMean secondWeight (response first)) ≤
      finiteMean secondWeight (fun second => finiteVariance firstWeight (fun first => response first second)) := by
  have centered (first : First) :
      finiteMean secondWeight (response first) -
        finiteMean firstWeight (fun first => finiteMean secondWeight (response first)) =
      finiteMean secondWeight (fun second => response first second -
        finiteMean firstWeight (fun first => response first second)) := by
    rw [finiteMean_swap]
    simp only [finiteMean, mul_sub, Finset.sum_sub_distrib]
  have bound (first : First) := finite_weighted_mean_sq_le secondWeight
    (fun second => response first second - finiteMean firstWeight (fun first => response first second))
    secondNonnegative secondNormalized
  unfold finiteVariance
  simp_rw [centered]
  calc
    _ ≤ ∑ first, firstWeight first *
        finiteMean secondWeight (fun second =>
          (response first second - finiteMean firstWeight (fun first => response first second)) ^ 2) := by
      apply Finset.sum_le_sum
      intro first _
      exact mul_le_mul_of_nonneg_left (bound first) (firstNonnegative first)
    _ = _ := finiteMean_swap firstWeight secondWeight _

theorem finite_product_variance_tensorization_two_blocks
    (firstWeight : First → ℝ) (secondWeight : Second → ℝ)
    (firstNonnegative : ∀ first, 0 ≤ firstWeight first)
    (secondNonnegative : ∀ second, 0 ≤ secondWeight second)
    (firstNormalized : ∑ first, firstWeight first = 1)
    (secondNormalized : ∑ second, secondWeight second = 1)
    (response : First → Second → ℝ) :
    finiteVariance (fun outcome : First × Second => firstWeight outcome.1 * secondWeight outcome.2)
      (fun outcome => response outcome.1 outcome.2) ≤
      finiteMean firstWeight (fun first => finiteVariance secondWeight (response first)) +
        finiteMean secondWeight (fun second => finiteVariance firstWeight (fun first => response first second)) := by
  rw [finiteVariance_product_decomposition firstWeight secondWeight firstNormalized secondNormalized]
  exact add_le_add le_rfl
    (variance_of_finite_average_le firstWeight secondWeight firstNonnegative secondNonnegative
      secondNormalized response)

end IGSIII34.Probability
