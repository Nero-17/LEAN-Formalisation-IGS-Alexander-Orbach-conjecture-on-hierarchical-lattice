import IGSIII34.Probability.InverseMoments

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Filter

theorem exists_positive_smallBall_start
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    [IsProbabilityMeasure measure] (value : Sample → ℝ)
    (measurable : Measurable value) (integrable : Integrable value measure)
    (nonnegative : ∀ᵐ sample ∂measure, 0 ≤ value sample)
    (meanPositive : 0 < ∫ sample, value sample ∂measure) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ measure.real {sample | value sample ≤ cutoff} < 1 := by
  by_contra absent
  push_neg at absent
  have smallAe (depth : ℕ) :
      ∀ᵐ sample ∂measure, value sample ≤ 1 / (depth + 1 : ℝ) := by
    have cutoffPositive : 0 < 1 / (depth + 1 : ℝ) := by positivity
    have realOne : measure.real {sample | value sample ≤ 1 / (depth + 1 : ℝ)} = 1 :=
      le_antisymm measureReal_le_one (absent _ cutoffPositive)
    have probabilityOne : measure {sample | value sample ≤ 1 / (depth + 1 : ℝ)} = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
      simpa only [Measure.real, ENNReal.toReal_one] using realOne
    exact (mem_ae_iff_prob_eq_one (measurableSet_le measurable measurable_const)).mpr probabilityOne
  have zeroAe : value =ᵐ[measure] 0 := by
    filter_upwards [ae_all_iff.mpr smallAe, nonnegative] with sample bounds lower
    change value sample = 0
    apply le_antisymm _ lower
    by_contra above
    obtain ⟨depth, strict⟩ := exists_nat_one_div_lt (lt_of_not_ge above)
    exact (strict.trans_le (bounds depth)).false
  have zeroMean : (∫ sample, value sample ∂measure) = 0 := by
    rw [integral_congr_ae zeroAe]
    simp
  exact (meanPositive.ne' zeroMean)

theorem positive_ae_of_smallBall_thinning_at_zero
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    [IsProbabilityMeasure measure] (value : Sample → ℝ)
    (nonnegative : ∀ᵐ sample ∂measure, 0 ≤ value sample)
    {cutoff : ℝ} (cutoffPositive : 0 < cutoff)
    (startBelowOne : measure.real {sample | value sample ≤ cutoff} < 1)
    (map : ℝ → ℝ)
    (strict : ∀ atom : ℝ, 0 < atom → atom < 1 → map atom < atom)
    (zeroRecursion : measure.real {sample | value sample ≤ 0} ≤
      map (measure.real {sample | value sample ≤ 0})) :
    ∀ᵐ sample ∂measure, 0 < value sample := by
  have atomBelowOne : measure.real {sample | value sample ≤ 0} < 1 :=
    (measureReal_mono fun _ small => small.trans cutoffPositive.le).trans_lt startBelowOne
  have atomZero : measure.real {sample | value sample ≤ 0} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra notZero
    have atomPositive : 0 < measure.real {sample | value sample ≤ 0} := lt_of_not_ge notZero
    exact (zeroRecursion.trans_lt (strict _ atomPositive atomBelowOne)).false
  have measureZero : measure {sample | value sample ≤ 0} = 0 := (measureReal_eq_zero_iff).mp atomZero
  apply ae_iff.mpr
  simpa only [not_lt] using measureZero

end
end IGSIII4
