import IGSIII4.SpectralDensity.ActualMomentLaplace20261012
import IGSIII34.Probability.FiniteProduct

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
open IGSIII34.Probability

theorem finiteMean_product_laplace20261012 {Coordinate Outcome : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Outcome]
    (weight response : Outcome → ℝ) :
    finiteMean (productWeight (Edge := Coordinate) weight)
      (fun outcome => Real.exp (-(∑ coordinate, response (outcome coordinate)) / 18)) =
        (finiteMean weight (fun outcome => Real.exp (-response outcome / 18))) ^
          Fintype.card Coordinate := by
  have exponential (outcome : Coordinate → Outcome) :
      Real.exp (-(∑ coordinate, response (outcome coordinate)) / 18) =
        ∏ coordinate, Real.exp (-response (outcome coordinate) / 18) := by
    have rewriteSum : -(∑ coordinate, response (outcome coordinate)) / 18 =
        ∑ coordinate, -response (outcome coordinate) / 18 := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    rw [rewriteSum, Real.exp_sum]
  simp only [finiteMean, productWeight, exponential, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Coordinate) (outcome : Outcome) =>
    weight outcome * Real.exp (-response outcome / 18))]
  simp

/-- Uniform lower-tail control for an actual independent finite product law. -/
theorem finiteMean_path_lower_tail20261012 {Coordinate Outcome : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Outcome]
    (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (responseNonnegative : ∀ outcome, 0 ≤ response outcome)
    (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    finiteMean (productWeight (Edge := Coordinate) weight)
      (fun outcome => if (∑ coordinate, response (outcome coordinate)) <
          (Fintype.card Coordinate : ℝ) / 2 then 1 else 0) ≤
        (69 / 70 : ℝ) ^ Fintype.card Coordinate := by
  classical
  have pointwise (outcome : Coordinate → Outcome) :
      (if (∑ coordinate, response (outcome coordinate)) <
          (Fintype.card Coordinate : ℝ) / 2 then (1 : ℝ) else 0) ≤
        Real.exp ((Fintype.card Coordinate : ℝ) / 36) *
          Real.exp (-(∑ coordinate, response (outcome coordinate)) / 18) := by
    rw [← Real.exp_add]
    split_ifs with below
    · exact Real.one_le_exp (by linarith)
    · exact (Real.exp_pos _).le
  have productNonnegative (outcome : Coordinate → Outcome) :
      0 ≤ productWeight weight outcome :=
    Finset.prod_nonneg (fun coordinate _ => weightNonnegative (outcome coordinate))
  have comparison := Finset.sum_le_sum (fun outcome (_ : outcome ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pointwise outcome) (productNonnegative outcome))
  change finiteMean (productWeight (Edge := Coordinate) weight) _ ≤ _ at comparison
  have factor : (∑ outcome : Coordinate → Outcome,
      productWeight weight outcome * (Real.exp ((Fintype.card Coordinate : ℝ) / 36) *
        Real.exp (-(∑ coordinate, response (outcome coordinate)) / 18))) =
      Real.exp ((Fintype.card Coordinate : ℝ) / 36) *
        finiteMean (productWeight (Edge := Coordinate) weight)
          (fun outcome => Real.exp (-(∑ coordinate, response (outcome coordinate)) / 18)) := by
    simp only [finiteMean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro outcome _
    ring
  rw [factor, finiteMean_product_laplace20261012] at comparison
  have expBound : Real.exp ((1 : ℝ) / 36) ≤ 36 / 35 := by
    convert Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 36) (by norm_num : (1 : ℝ) / 36 < 1) using 1 <;> norm_num
  have productBound : Real.exp ((1 : ℝ) / 36) *
      finiteMean weight (fun outcome => Real.exp (-response outcome / 18)) ≤ 69 / 70 := by
    have laplace := finiteMean_laplace_le20261012 weight response weightNonnegative
      normalized responseNonnegative meanOne varianceBound
    have nonnegativeMean : 0 ≤ finiteMean weight (fun outcome => Real.exp (-response outcome / 18)) :=
      Finset.sum_nonneg (fun outcome _ => mul_nonneg (weightNonnegative outcome) (Real.exp_pos _).le)
    calc
      _ ≤ (36 / 35 : ℝ) * (23 / 24) :=
        mul_le_mul expBound laplace nonnegativeMean (by norm_num)
      _ = _ := by norm_num
  have positiveProduct : 0 ≤ Real.exp ((1 : ℝ) / 36) *
      finiteMean weight (fun outcome => Real.exp (-response outcome / 18)) := by
    apply mul_nonneg (Real.exp_pos _).le
    exact Finset.sum_nonneg (fun outcome _ => mul_nonneg (weightNonnegative outcome) (Real.exp_pos _).le)
  have powerBound := pow_le_pow_left₀ positiveProduct productBound (Fintype.card Coordinate)
  have exponential : Real.exp ((Fintype.card Coordinate : ℝ) / 36) =
      Real.exp ((1 : ℝ) / 36) ^ Fintype.card Coordinate := by
    convert Real.exp_nat_mul ((1 : ℝ) / 36) (Fintype.card Coordinate) using 1 <;> ring
  rw [exponential, ← mul_pow] at comparison
  exact comparison.trans powerBound

end
end IGSIII4.SpectralDensity
