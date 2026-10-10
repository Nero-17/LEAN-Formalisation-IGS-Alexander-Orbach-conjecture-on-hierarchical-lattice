import IGSIII34.Percolation.ConfigurationVariance
import IGSIII.Chemical.GeodesicMixtureEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators

theorem finite_electricalCell_mixture_variance_le_product_moments
    {vertices edges : ℕ} {State : Type*} [Fintype State]
    (rule : Universality.FiniteNetwork vertices edges)
    (rootWeight : Configuration edges → ℝ) (rootNonnegative : ∀ configuration, 0 ≤ rootWeight configuration)
    (rootNormalized : ∑ configuration, rootWeight configuration = 1)
    (rootSupported : ∀ configuration, rule.crosses configuration ≠ true → rootWeight configuration = 0)
    (weight : State → ℝ) (nonnegative : ∀ state, 0 ≤ weight state)
    (normalized : ∑ state, weight state = 1)
    (resistance : State → ℝ) (positive : ∀ state, 0 < resistance state)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondBound : finiteMean weight (fun state => resistance state^2) ≤ secondMoment)
    (inverseBound : finiteMean weight (fun state => (resistance state)⁻¹^power) ≤ inverseMoment) :
    finiteMean rootWeight (fun configuration =>
      finiteVariance (tupleWeight (fun _ : Fin edges => weight))
        (fun input : Fin edges → State => electricalCell rule configuration (fun edge => resistance (input edge)))) ≤
      2*secondMoment *
        (finiteMean rootWeight (fun configuration =>
          finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
            electricalCell rule configuration (fun edge => resistance (input edge))^2)))^(1/(2 : ℝ)) *
              ((edges : ℝ)*inverseMoment)^(1/power) := by
  have outputNonnegative (configuration : Configuration edges) : 0 ≤
      finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
        electricalCell rule configuration (fun edge => resistance (input edge))^2) := by
    unfold finiteMean
    exact Finset.sum_nonneg (fun input _ => mul_nonneg
      (tupleWeight_nonnegative _ (fun _ => nonnegative) input) (sq_nonneg _))
  have rootBound := IGSIII.Chemical.finiteMean_sqrt_rpow_le rootWeight
    (fun configuration => finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
      electricalCell rule configuration (fun edge => resistance (input edge))^2)) rootNonnegative rootNormalized outputNonnegative
  calc
    _ ≤ finiteMean rootWeight (fun configuration => 2*secondMoment *
        (finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
          electricalCell rule configuration (fun edge => resistance (input edge))^2))^(1/(2 : ℝ)) *
            ((edges : ℝ)*inverseMoment)^(1/power)) := by
      unfold finiteMean
      apply Finset.sum_le_sum
      intro configuration _
      by_cases crossing : rule.crosses configuration = true
      · apply mul_le_mul_of_nonneg_left _ (rootNonnegative configuration)
        apply (finite_electricalCell_variance_le_product_moments rule configuration crossing weight nonnegative normalized
          resistance positive powerAtLeastTwo inverseMoment inverseBound).trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) inverseMomentNonnegative) _)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (outputNonnegative configuration) _)
        exact mul_le_mul_of_nonneg_left secondBound (by norm_num)
      · simp only [rootSupported configuration crossing, zero_mul, le_refl]
    _ = 2*secondMoment * finiteMean rootWeight (fun configuration =>
        (finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
          electricalCell rule configuration (fun edge => resistance (input edge))^2))^(1/(2 : ℝ))) *
            ((edges : ℝ)*inverseMoment)^(1/power) := by
      unfold finiteMean
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left rootBound (mul_nonneg (by norm_num) secondMomentNonnegative))
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) inverseMomentNonnegative) _)

end
end IGSIII34.Percolation
