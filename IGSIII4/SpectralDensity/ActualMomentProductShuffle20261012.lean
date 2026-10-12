import IGSIII4.SpectralDensity.ActualMomentLongLaw20261012
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
open IGSIII34.Probability
attribute [local instance] Classical.propDecidable

def pairedInputEquiv (Index First Second : Type*) :
    ((Index → First) × (Index → Second)) ≃ (Index → First × Second) where
  toFun input index := (input.1 index, input.2 index)
  invFun input := (fun index => (input index).1, fun index => (input index).2)
  left_inv input := rfl
  right_inv input := rfl

theorem finiteMean_product_shuffle20261012 {Index First Second : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype First] [Fintype Second]
    (firstWeight : First → ℝ) (secondWeight : Second → ℝ)
    (observable : (Index → First) → (Index → Second) → ℝ) :
    finiteMean (productWeight firstWeight) (fun first =>
      finiteMean (productWeight secondWeight) (observable first)) =
        finiteMean (productWeight (fun pair : First × Second => firstWeight pair.1 * secondWeight pair.2))
          (fun input => observable (fun index => (input index).1) (fun index => (input index).2)) := by
  rw [← finiteMean_product (productWeight firstWeight) (productWeight secondWeight) observable]
  unfold finiteMean
  rw [← (pairedInputEquiv Index First Second).sum_comp
    (fun input => productWeight (fun pair : First × Second => firstWeight pair.1 * secondWeight pair.2) input *
      observable (fun index => (input index).1) (fun index => (input index).2))]
  apply Finset.sum_congr rfl
  intro input _
  simp only [pairedInputEquiv, Equiv.coe_fn_mk, productWeight, Finset.prod_mul_distrib]

def fourInputEquiv (Outcome : Type*) : (Fin 4 → Outcome) ≃ (Outcome × Outcome) × (Outcome × Outcome) where
  toFun input := ((input 0, input 1), (input 2, input 3))
  invFun input := ![input.1.1, input.1.2, input.2.1, input.2.2]
  left_inv input := by funext edge; fin_cases edge <;> rfl
  right_inv input := by rcases input with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl

theorem finiteMean_four_shuffle20261012 {Outcome : Type*} [Fintype Outcome]
    (weight : Outcome → ℝ) (observable : (Outcome × Outcome) → (Outcome × Outcome) → ℝ) :
    finiteMean (productWeight weight) (fun input : Fin 4 → Outcome => observable (input 0, input 1) (input 2, input 3)) =
      finiteMean (fun input : Outcome × Outcome => weight input.1 * weight input.2) (fun first =>
        finiteMean (fun input : Outcome × Outcome => weight input.1 * weight input.2) (observable first)) := by
  rw [← finiteMean_product (fun input : Outcome × Outcome => weight input.1 * weight input.2)
    (fun input : Outcome × Outcome => weight input.1 * weight input.2) observable]
  unfold finiteMean
  rw [← (fourInputEquiv Outcome).sum_comp (fun input =>
    ((weight input.1.1 * weight input.1.2) * (weight input.2.1 * weight input.2.2)) * observable input.1 input.2)]
  apply Finset.sum_congr rfl
  intro input _
  simp only [productWeight, Fin.prod_univ_four, fourInputEquiv, Equiv.coe_fn_mk]
  ring

end
end IGSIII4.SpectralDensity

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability
attribute [local instance] Classical.propDecidable

theorem conditionalActualChainWeight20261012 (blocks paths length : ℕ) (probability : ℝ)
    (configuration : Fin blocks → Fin paths → Configuration length) :
    productWeight (conditionalActualBlockWeight paths length probability) configuration =
      (if chainCrossing blocks paths length configuration then chainWeight blocks paths length probability configuration else 0) /
        (1 - (1 - probability ^ length) ^ paths) ^ blocks := by
  by_cases crossing : chainCrossing blocks paths length configuration
  · simp only [crossing, ↓reduceIte, productWeight, conditionalActualBlockWeight,
      show ∀ block, blockCrossing paths length (configuration block) from crossing, ↓reduceIte,
      Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, chainWeight]
  · have failed : ∃ block, ¬blockCrossing paths length (configuration block) := by
      by_contra h
      apply crossing
      intro block
      exact not_not.mp (fun fail => h ⟨block,fail⟩)
    obtain ⟨block, failed⟩ := failed
    simp only [crossing, ↓reduceIte, zero_div]
    exact Finset.prod_eq_zero (Finset.mem_univ block) (by simp [conditionalActualBlockWeight, failed])

theorem actualLong_second_moment_bound20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (probabilityNonnegative : 0 ≤ probability)
    (probabilityAtMostOne : probability ≤ 1) (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (lengthPositive : 0 < length) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    finiteMean (actualLongWeight blocks paths length probability weight)
      (fun input => actualLongResponse blocks paths length response input ^ 2) ≤
      (finiteMean (actualLongWeight blocks paths length probability weight) (actualLongResponse blocks paths length response)) ^ 2 +
        16 + (blocks : ℝ) * ((length : ℝ) ^ 2 + 8 * length) := by
  have bound := actualLong_variance_bound20261012 blocks paths length probability probabilityNonnegative probabilityAtMostOne
    crossingPositive weight response weightNonnegative normalized positive lengthPositive meanOne varianceBound
  rw [finiteVariance_eq_second_moment _ _ (actualLongWeight_normalized20261012 blocks paths length probability crossingPositive weight normalized)] at bound
  linarith

end
end IGSIII4.SpectralDensity.ActualFamily
