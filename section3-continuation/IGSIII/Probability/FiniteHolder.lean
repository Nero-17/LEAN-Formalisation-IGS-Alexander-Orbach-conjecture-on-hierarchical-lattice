import IGSIII.Probability.FiniteTensorization
import Mathlib.Analysis.MeanInequalities

/-! Weighted finite Hölder estimates for geodesic influences. -/

set_option autoImplicit false

namespace IGSIII.Probability

open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome]

theorem finiteMean_mul_le_holder
    (weight first second : Outcome → ℝ) {p q : ℝ}
    (conjugate : p.HolderConjugate q)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (firstNonnegative : ∀ outcome, 0 ≤ first outcome)
    (secondNonnegative : ∀ outcome, 0 ≤ second outcome) :
    finiteMean weight (fun outcome => first outcome * second outcome) ≤
      (finiteMean weight (fun outcome => first outcome ^ p)) ^ (1 / p) *
        (finiteMean weight (fun outcome => second outcome ^ q)) ^ (1 / q) := by
  have factor (outcome : Outcome) :
      (weight outcome ^ (1 / p) * first outcome) *
          (weight outcome ^ (1 / q) * second outcome) =
        weight outcome * (first outcome * second outcome) := by
    calc
      _ = (weight outcome ^ (1 / p) * weight outcome ^ (1 / q)) *
          (first outcome * second outcome) := by ring
      _ = weight outcome ^ (1 / p + 1 / q) *
          (first outcome * second outcome) := by
            rw [Real.rpow_add_of_nonneg (weightNonnegative outcome)
              conjugate.one_div_nonneg conjugate.symm.one_div_nonneg]
      _ = _ := by rw [conjugate.one_div_add_one_div]; simp
  have firstPower (outcome : Outcome) :
      (weight outcome ^ (1 / p) * first outcome) ^ p =
        weight outcome * first outcome ^ p := by
    rw [Real.mul_rpow (Real.rpow_nonneg (weightNonnegative outcome) _) (firstNonnegative outcome)]
    rw [one_div, Real.rpow_inv_rpow (weightNonnegative outcome) conjugate.ne_zero]
  have secondPower (outcome : Outcome) :
      (weight outcome ^ (1 / q) * second outcome) ^ q =
        weight outcome * second outcome ^ q := by
    rw [Real.mul_rpow (Real.rpow_nonneg (weightNonnegative outcome) _) (secondNonnegative outcome)]
    rw [one_div, Real.rpow_inv_rpow (weightNonnegative outcome) conjugate.symm.ne_zero]
  have bound := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset Outcome)
    (f := fun outcome => weight outcome ^ (1 / p) * first outcome)
    (g := fun outcome => weight outcome ^ (1 / q) * second outcome) conjugate
    (fun outcome _ => mul_nonneg (Real.rpow_nonneg (weightNonnegative outcome) _) (firstNonnegative outcome))
    (fun outcome _ => mul_nonneg (Real.rpow_nonneg (weightNonnegative outcome) _) (secondNonnegative outcome))
  simpa only [factor, firstPower, secondPower, finiteMean] using bound

theorem finiteMean_mul_indicator_le_holder
    (weight response : Outcome → ℝ) (event : Outcome → Prop) [DecidablePred event]
    {p q : ℝ} (conjugate : p.HolderConjugate q)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (responseNonnegative : ∀ outcome, 0 ≤ response outcome) :
    finiteMean weight (fun outcome => response outcome * if event outcome then 1 else 0) ≤
      (finiteMean weight (fun outcome => response outcome ^ p)) ^ (1 / p) *
        (finiteMean weight (fun outcome => if event outcome then 1 else 0)) ^ (1 / q) := by
  have indicatorNonnegative (outcome : Outcome) :
      (0 : ℝ) ≤ if event outcome then 1 else 0 := by split_ifs <;> norm_num
  have indicatorPower (outcome : Outcome) :
      (if event outcome then (1 : ℝ) else 0) ^ q =
        if event outcome then (1 : ℝ) else 0 := by
    split_ifs <;> simp [Real.zero_rpow conjugate.symm.ne_zero]
  simpa only [indicatorPower] using
    finiteMean_mul_le_holder weight response (fun outcome => if event outcome then 1 else 0)
      conjugate weightNonnegative responseNonnegative indicatorNonnegative

end IGSIII.Probability
