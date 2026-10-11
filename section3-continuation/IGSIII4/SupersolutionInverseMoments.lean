import IGSIII4.SupersolutionSmallBall
import IGSIII4.ThinningInverseMoments
import Universality.Graph.ClassicalRule

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII34.Percolation
open scoped NNReal ENNReal

theorem supersolution_positive_and_inverse_moments (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value)
    (integrable : Integrable (fun marks => (value marks : ℝ))
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (meanPositive : 0 < ∫ marks, (value marks : ℝ)
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    {factor : ℝ} (factorPositive : 0 < factor)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      (electricalTransferNNReal rule value marks : ℝ) ≤ factor * (value marks : ℝ)) :
    (∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      0 < (value marks : ℝ)) ∧
    ∀ power : ℕ, Integrable (fun marks => (value marks : ℝ)⁻¹ ^ power)
      (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
  have realMeasurable : Measurable (fun marks => (value marks : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      0 ≤ (value marks : ℝ) := ae_of_all _ (fun marks => (value marks).property)
  obtain ⟨cutoff, cutoffPositive, startBelowOne⟩ := exists_positive_smallBall_start
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (fun marks => (value marks : ℝ)) realMeasurable integrable nonnegative meanPositive
  have zeroRecursion := supersolution_smallBall_recursion rule probability positive belowOne fixedPoint
    value measurable factorPositive (show (0 : ℝ) ≤ 0 from le_rfl) supersolution
  simp only [mul_zero] at zeroRecursion
  have valuePositive := positive_ae_of_smallBall_thinning_at_zero
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (fun marks => (value marks : ℝ)) nonnegative cutoffPositive startBelowOne
    (IGSIII34.Probability.thinningMap rule.network probability)
    (fun atom atomPositive atomBelowOne => IGSIII34.Probability.thinningMap_strict rule.network
      positive belowOne fixedPoint classicalRule.scale atomPositive atomBelowOne) zeroRecursion
  refine ⟨valuePositive, fun power => ?_⟩
  have baseAboveOne : 1 < max (2 : ℝ) ((rule.edges : ℝ) * factor) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have basePositive : 0 < max (2 : ℝ) ((rule.edges : ℝ) * factor) := zero_lt_one.trans baseAboveOne
  apply integrable_inv_pow_of_thinning_recursion_ae rule.network
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (fun marks => (value marks : ℝ)) realMeasurable valuePositive power positive belowOne fixedPoint
    classicalRule.scale baseAboveOne cutoffPositive startBelowOne
  intro depth
  have thresholdNonnegative : 0 ≤ cutoff / (max (2 : ℝ) ((rule.edges : ℝ) * factor)) ^ (depth + 1) :=
    (div_pos cutoffPositive (pow_pos basePositive _)).le
  have first := supersolution_smallBall_recursion rule probability positive belowOne fixedPoint
    value measurable factorPositive thresholdNonnegative supersolution
  apply first.trans
  apply IGSIII34.Probability.thinningMap_monotoneOn rule.network positive belowOne
    ⟨measureReal_nonneg, measureReal_le_one⟩ ⟨measureReal_nonneg, measureReal_le_one⟩
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro marks small
  change (value marks : ℝ) ≤ (rule.edges : ℝ) * factor *
    (cutoff / (max (2 : ℝ) ((rule.edges : ℝ) * factor)) ^ (depth + 1)) at small
  change (value marks : ℝ) ≤ cutoff / (max (2 : ℝ) ((rule.edges : ℝ) * factor)) ^ depth
  apply small.trans
  calc
    (rule.edges : ℝ) * factor *
        (cutoff / (max (2 : ℝ) ((rule.edges : ℝ) * factor)) ^ (depth + 1)) ≤
      max (2 : ℝ) ((rule.edges : ℝ) * factor) *
        (cutoff / (max (2 : ℝ) ((rule.edges : ℝ) * factor)) ^ (depth + 1)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) thresholdNonnegative
    _ = cutoff / (max (2 : ℝ) ((rule.edges : ℝ) * factor)) ^ depth := by
      rw [pow_succ]
      field_simp [basePositive.ne']

end
end IGSIII4
