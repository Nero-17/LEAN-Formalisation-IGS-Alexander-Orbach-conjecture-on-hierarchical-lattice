import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace Universality
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Turn a normalized nonnegative finite real weight into a probability law. -/
def finiteWeightPMF {α : Type*} [Fintype α] (weight : α → ℝ)
    (hnonneg : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (weight a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hnonneg a), hsum]
    simp)

@[simp] theorem finiteWeightPMF_apply {α : Type*} [Fintype α] (weight : α → ℝ)
    (hnonneg : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1) (a : α) :
    finiteWeightPMF weight hnonneg hsum a = ENNReal.ofReal (weight a) := rfl

@[simp] theorem finiteWeightPMF_singleton {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (weight : α → ℝ)
    (hnonneg : ∀ a, 0 ≤ weight a) (hsum : ∑ a, weight a = 1) (a : α) :
    (finiteWeightPMF weight hnonneg hsum).toMeasure {a} =
      ENNReal.ofReal (weight a) :=
  PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

def finiteWeightKernel {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (weight : α → β → ℝ)
    (hnonneg : ∀ a b, 0 ≤ weight a b) (hsum : ∀ a, ∑ b, weight a b = 1) :
    Kernel α β :=
  Kernel.ofFunOfCountable (fun a => (finiteWeightPMF (weight a) (hnonneg a) (hsum a)).toMeasure)

instance {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (weight : α → β → ℝ) (hnonneg : ∀ a b, 0 ≤ weight a b)
    (hsum : ∀ a, ∑ b, weight a b = 1) :
    IsMarkovKernel (finiteWeightKernel weight hnonneg hsum) where
  isProbabilityMeasure a := inferInstanceAs (IsProbabilityMeasure
    (finiteWeightPMF (weight a) (hnonneg a) (hsum a)).toMeasure)

@[simp] theorem finiteWeightKernel_singleton {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (weight : α → β → ℝ) (hnonneg : ∀ a b, 0 ≤ weight a b)
    (hsum : ∀ a, ∑ b, weight a b = 1) (a : α) (b : β) :
    finiteWeightKernel weight hnonneg hsum a {b} = ENNReal.ofReal (weight a b) :=
  finiteWeightPMF_singleton _ _ _ _

theorem finiteWeightKernel_comp {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (weight : α → β → ℝ) (hnonneg : ∀ a b, 0 ≤ weight a b)
    (hsum : ∀ a, ∑ b, weight a b = 1)
    (before : α → ℝ) (hbefore : ∀ a, 0 ≤ before a) (hsbefore : ∑ a, before a = 1)
    (after : β → ℝ) (hafter : ∀ b, 0 ≤ after b) (hsafter : ∑ b, after b = 1)
    (hstep : ∀ b, ∑ a, before a * weight a b = after b) :
    finiteWeightKernel weight hnonneg hsum ∘ₘ (finiteWeightPMF before hbefore hsbefore).toMeasure =
      (finiteWeightPMF after hafter hsafter).toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.bind_apply (measurableSet_singleton b) (Kernel.aemeasurable _)]
  rw [lintegral_countable']
  simp only [tsum_fintype, finiteWeightKernel_singleton, finiteWeightPMF_singleton]
  simp_rw [mul_comm (ENNReal.ofReal (weight _ b)), ← ENNReal.ofReal_mul (hbefore _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hbefore a) (hnonneg a b)),
    hstep]

end
end Universality
