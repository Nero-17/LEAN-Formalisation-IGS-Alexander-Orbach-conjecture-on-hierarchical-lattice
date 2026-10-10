import IGSIII.Chemical.GeodesicProductEstimate

/-! Averaging the actual conditional finite-product variance over an outer graph. -/

set_option autoImplicit false

namespace IGSIII.Chemical

open IGSIII.Probability PathFamily
open scoped BigOperators

variable {Root Outcome : Type*} [Fintype Root] [Fintype Outcome] {count : ℕ}

theorem finiteMean_sqrt_rpow_le (weight response : Root → ℝ)
    (weightNonnegative : ∀ root, 0 ≤ weight root)
    (normalized : ∑ root, weight root = 1)
    (responseNonnegative : ∀ root, 0 ≤ response root) :
    finiteMean weight (fun root => response root ^ (1 / (2 : ℝ))) ≤
      (finiteMean weight response) ^ (1 / (2 : ℝ)) := by
  have bound := (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1)).le_map_sum
    (t := Finset.univ) (w := weight) (p := response)
    (fun root _ => weightNonnegative root) normalized (fun root _ => responseNonnegative root)
  simpa only [finiteMean, smul_eq_mul] using bound

theorem shortest_mixture_variance_le_product_moments
    (rootWeight : Root → ℝ) (family : Root → PathFamily (Fin count))
    (weight localCost : Root → Fin count → Outcome → ℝ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (rootNonnegative : ∀ root, 0 ≤ rootWeight root)
    (rootNormalized : ∑ root, rootWeight root = 1)
    (weightNonnegative : ∀ root edge outcome, 0 ≤ weight root edge outcome)
    (normalized : ∀ root edge, ∑ outcome, weight root edge outcome = 1)
    (positive : ∀ root edge outcome, 0 < localCost root edge outcome)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ root edge,
      finiteMean (weight root edge) (fun outcome => localCost root edge outcome ^ 2) ≤ secondMoment)
    (inverseMomentBound : ∀ root edge,
      finiteMean (weight root edge) (fun outcome => (localCost root edge outcome)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean rootWeight (fun root => finiteVariance (tupleWeight (weight root))
      (fun outcome => (family root).shortest (sampledEdgeCost (localCost root) outcome))) ≤
      2 * secondMoment *
        (finiteMean rootWeight (fun root => finiteMean (tupleWeight (weight root))
          (fun outcome => (family root).shortest (sampledEdgeCost (localCost root) outcome) ^ 2))) ^
            (1 / (2 : ℝ)) * ((count : ℝ) * inverseMoment) ^ (1 / power) := by
  have outputNonnegative (root : Root) : 0 ≤ finiteMean (tupleWeight (weight root))
      (fun outcome => (family root).shortest (sampledEdgeCost (localCost root) outcome) ^ 2) := by
    unfold finiteMean
    exact Finset.sum_nonneg (fun outcome _ =>
      mul_nonneg (tupleWeight_nonnegative _ (weightNonnegative root) outcome) (sq_nonneg _))
  have meanBound := finiteMean_sqrt_rpow_le rootWeight
    (fun root => finiteMean (tupleWeight (weight root))
      (fun outcome => (family root).shortest (sampledEdgeCost (localCost root) outcome) ^ 2))
    rootNonnegative rootNormalized outputNonnegative
  calc
    _ ≤ finiteMean rootWeight (fun root => 2 * secondMoment *
        (finiteMean (tupleWeight (weight root))
          (fun outcome => (family root).shortest (sampledEdgeCost (localCost root) outcome) ^ 2)) ^
            (1 / (2 : ℝ)) * ((count : ℝ) * inverseMoment) ^ (1 / power)) := by
      unfold finiteMean
      apply Finset.sum_le_sum
      intro root _
      exact mul_le_mul_of_nonneg_left
        (shortest_variance_le_product_moment_bound (family root) (weight root) (localCost root)
          powerAtLeastTwo (weightNonnegative root) (normalized root) (positive root)
          secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
          (secondMomentBound root) (inverseMomentBound root)) (rootNonnegative root)
    _ = 2 * secondMoment * finiteMean rootWeight (fun root =>
        (finiteMean (tupleWeight (weight root))
          (fun outcome => (family root).shortest (sampledEdgeCost (localCost root) outcome) ^ 2)) ^
            (1 / (2 : ℝ))) * ((count : ℝ) * inverseMoment) ^ (1 / power) := by
      unfold finiteMean
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro root _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left meanBound (mul_nonneg (by norm_num) secondMomentNonnegative))
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg count) inverseMomentNonnegative) _)

end IGSIII.Chemical
