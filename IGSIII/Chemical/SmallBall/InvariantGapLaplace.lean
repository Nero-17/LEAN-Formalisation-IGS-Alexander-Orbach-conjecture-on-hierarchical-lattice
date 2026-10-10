import IGSIII.Chemical.SmallBall.Laplace

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {Sample Index : Type*} [MeasurableSpace Sample]

theorem exists_uniform_smallBall_start_of_positive_mean
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) (measurable : ∀ index, Measurable (value index))
    (integrable : ∀ index, Integrable (value index) measure)
    (squareIntegrable : ∀ index, Integrable (fun sample => value index sample ^ 2) measure)
    {gap bound : ℝ} (gapPositive : 0 < gap) (boundNonnegative : 0 ≤ bound)
    (meanLower : ∀ index, gap ≤ ∫ sample, value index sample ∂measure)
    (secondMomentBound : ∀ index, (∫ sample, value index sample ^ 2 ∂measure) ≤ bound) :
    ∃ start : ℝ, 0 ≤ start ∧ start < 1 ∧
      ∀ index, measure.real {sample | value index sample ≤ gap / 2} ≤ start := by
  have meanPositive (index : Index) : 0 < ∫ sample, value index sample ∂measure :=
    gapPositive.trans_le (meanLower index)
  have normalizedSecondBound (index : Index) :
      (∫ sample, (value index sample / (∫ sample, value index sample ∂measure)) ^ 2 ∂measure) ≤
        max 1 (bound / gap ^ 2) := by
    simp only [div_pow, integral_div]
    calc
      (∫ sample, value index sample ^ 2 ∂measure) /
          (∫ sample, value index sample ∂measure) ^ 2 ≤
        bound / (∫ sample, value index sample ∂measure) ^ 2 :=
          div_le_div_of_nonneg_right (secondMomentBound index) (sq_nonneg _)
      _ ≤ bound / gap ^ 2 := div_le_div_of_nonneg_left boundNonnegative
        (sq_pos_of_pos gapPositive) (pow_le_pow_left₀ gapPositive.le (meanLower index) 2)
      _ ≤ max 1 (bound / gap ^ 2) := le_max_right _ _
  obtain ⟨start, startNonnegative, startBelowOne, startBound⟩ :=
    exists_uniform_smallBall_start_of_second_moment_bound measure
      (fun index sample => value index sample / (∫ sample, value index sample ∂measure))
      (fun index => (measurable index).div_const _)
      (fun index => (integrable index).div_const _)
      (fun index => by simpa only [div_pow] using
        (squareIntegrable index).div_const ((∫ sample, value index sample ∂measure) ^ 2))
      (fun index => by rw [integral_div, div_self (meanPositive index).ne'])
      (le_max_left 1 (bound / gap ^ 2)) normalizedSecondBound
  refine ⟨start, startNonnegative, startBelowOne, fun index => ?_⟩
  apply (measureReal_mono (μ := measure) (show
      {sample | value index sample ≤ gap / 2} ⊆
        {sample | value index sample / (∫ sample, value index sample ∂measure) ≤ 1 / 2} from ?_)).trans
      (startBound index)
  intro sample small
  change value index sample ≤ gap / 2 at small
  change value index sample / (∫ sample, value index sample ∂measure) ≤ 1 / 2
  apply (div_le_iff₀ (meanPositive index)).mpr
  linarith [meanLower index]

theorem invariant_family_thinning_tail_bound
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) (successor : Index → Index) (onto : Function.Surjective successor)
    {critical start base cutoff : ℝ}
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1) (basePositive : 0 < base)
    (initial : ∀ index, measure.real {sample | value index sample ≤ cutoff} ≤ start)
    (step : ∀ index threshold, measure.real {sample | value (successor index) sample ≤ threshold} ≤
      thinningMap network critical (measure.real {sample | value index sample ≤ base * threshold})) :
    ∀ depth index, measure.real {sample | value index sample ≤ cutoff / base ^ depth} ≤
      (thinningMap network critical)^[depth] start := by
  have orbitBounds := iterate_bounds startNonnegative startBelowOne
    (thinningMap_zero network critical)
    (fun input nonnegative belowOne => thinningMap_nonnegative network criticalPositive criticalBelowOne nonnegative belowOne.le)
    (fun input positive belowOne => thinningMap_strict network criticalPositive criticalBelowOne fixedPoint scale positive belowOne)
  intro depth
  induction depth with
  | zero => simpa only [pow_zero, div_one, Function.iterate_zero_apply] using initial
  | succ depth inductionHypothesis =>
      intro index
      obtain ⟨preimage, rfl⟩ := onto index
      have thresholdIdentity : base * (cutoff / base ^ (depth + 1)) = cutoff / base ^ depth := by
        rw [pow_succ]
        field_simp
      have comparison := step preimage (cutoff / base ^ (depth + 1))
      rw [thresholdIdentity] at comparison
      rw [Function.iterate_succ_apply']
      apply comparison.trans
      apply thinningMap_monotoneOn network criticalPositive criticalBelowOne
        ⟨measureReal_nonneg, measureReal_le_one⟩
        ⟨(orbitBounds depth).1, (orbitBounds depth).2.trans startBelowOne.le⟩
      exact inductionHypothesis preimage

theorem exists_uniform_laplace_bound_ae
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) (measurable : ∀ index, Measurable (value index))
    (nonnegative : ∀ index, 0 ≤ᵐ[measure] value index)
    (smallBalls : ∀ error : ℝ, 0 < error → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ index, measure.real {sample | value index sample ≤ cutoff} ≤ error)
    {target : ℝ} (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ index,
      (∫ sample, Real.exp (-parameter * value index sample) ∂measure) ≤ target := by
  obtain ⟨parameter, parameterPositive, bound⟩ := exists_uniform_laplace_bound measure
    (fun index sample => max 0 (value index sample))
    (fun index => measurable_const.max (measurable index)) (fun _ _ => le_max_left _ _)
    (fun error errorPositive => by
      obtain ⟨cutoff, cutoffPositive, valid⟩ := smallBalls error errorPositive
      refine ⟨cutoff, cutoffPositive, fun index => ?_⟩
      apply (measureReal_mono (μ := measure) (show
        {sample | max 0 (value index sample) ≤ cutoff} ⊆ {sample | value index sample ≤ cutoff} from
          fun sample small => (le_max_right (0 : ℝ) (value index sample)).trans small)).trans (valid index)) targetPositive
  refine ⟨parameter, parameterPositive, fun index => ?_⟩
  have equality : (fun sample => Real.exp (-parameter * value index sample)) =ᵐ[measure]
      fun sample => Real.exp (-parameter * max 0 (value index sample)) := by
    filter_upwards [nonnegative index] with sample positive
    change 0 ≤ value index sample at positive
    rw [max_eq_right positive]
  exact (integral_congr_ae equality).le.trans (bound index)

theorem exists_uniform_laplace_bound_of_invariant_thinning
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) (measurable : ∀ index, Measurable (value index))
    (nonnegative : ∀ index, 0 ≤ᵐ[measure] value index)
    (successor : Index → Index) (onto : Function.Surjective successor)
    {critical start base cutoff target : ℝ}
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (basePositive : 0 < base) (cutoffPositive : 0 < cutoff)
    (initial : ∀ index, measure.real {sample | value index sample ≤ cutoff} ≤ start)
    (step : ∀ index threshold, measure.real {sample | value (successor index) sample ≤ threshold} ≤
      thinningMap network critical (measure.real {sample | value index sample ≤ base * threshold}))
    (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ index,
      (∫ sample, Real.exp (-parameter * value index sample) ∂measure) ≤ target := by
  apply exists_uniform_laplace_bound_ae measure value measurable nonnegative _ targetPositive
  apply exists_uniform_smallBall_cutoff_of_thinning_bound network measure value criticalPositive criticalBelowOne
    fixedPoint scale startNonnegative startBelowOne basePositive cutoffPositive
  intro index depth
  exact invariant_family_thinning_tail_bound network measure value successor onto criticalPositive criticalBelowOne
    fixedPoint scale startNonnegative startBelowOne basePositive initial step depth index

end
end IGSIII.Chemical.SmallBall
